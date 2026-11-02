(* ::Package:: *)

(* LatticeLoops.wl
   Killed simple random walk on regions of Z^2.

   Conventions
   - A site is an integer pair {x, y}.
   - A region is just a List of sites. Its order fixes the row/column
     order of every matrix built from it.
   - P_D is the transition matrix of simple random walk killed on leaving D:
       (P_D)[[i, j]] = 1/4 if sites i and j are nearest neighbours, else 0.
     Entries are exact (1/4); wrap in N[] for numerics.

   Usage
     Get["LatticeLoops.wl"]           (* or Needs, if it's on $Path *)
     disk = DiskSites[6];
     ann  = AnnulusSites[6, 12];      (* 6 <= r < 12 *)
     P    = TransitionMatrix[disk];
     Q    = HoppingBlock[disk, ann];  (* disk -> annulus block of P_{disk u ann} *)
     cut  = CutEdges[disk, ann];      (* directed edges crossing the circle r = 6 *)
     ShowSites[{disk, ann}, cut]

     (* sphere = two disk vacua glued along the circle *)
     Psph = GluedTransitionMatrix[DiskSites[10, "Center" -> {1/2, 1/2}]];
     PinnedLoopMass[Psph]             (* zero mode pinned; see usage *)
*)

BeginPackage["LatticeLoops`"];

RegionSites::usage =
  "RegionSites[pred, {xmin, xmax}, {ymin, ymax}] gives the sites {x, y} in the box \
for which pred[{x, y}] is True, ordered lexicographically.";

DiskSites::usage =
  "DiskSites[R] gives the sites with |{x, y} - c| < R. \
Option \"Center\" -> c (default {0, 0}; try {1/2, 1/2} to center on a plaquette).";

AnnulusSites::usage =
  "AnnulusSites[r, R] gives the sites with r <= |{x, y} - c| < R. \
Option \"Center\" as for DiskSites. DiskSites[r] and AnnulusSites[r, R] \
partition DiskSites[R].";

HoppingBlock::usage =
  "HoppingBlock[from, to] gives the block of the random-walk transition matrix with \
rows indexed by the sites in from and columns by the sites in to: 1/4 for nearest \
neighbours, 0 otherwise. Returns a SparseArray.";

TransitionMatrix::usage =
  "TransitionMatrix[sites] gives P_D, the transition matrix of simple random walk \
killed on leaving the region, as a SparseArray. Same as HoppingBlock[sites, sites].";

GreensFunction::usage =
  "GreensFunction[sites] gives m = (1 - P_D)^-1 numerically, as a dense matrix. \
m[[i, j]] is the total mass of walks from site i to site j that stay in the region.";

LoopMass::usage =
  "LoopMass[sites] gives the total rooted loop mass -Log[Det[1 - P_D]] numerically.";

GluedTransitionMatrix::usage =
  "GluedTransitionMatrix[sites] glues two copies of the region along its cut edges: \
every edge that leaves copy 1 lands on the twin site in copy 2, and vice versa. \
Indices 1..n are copy 1, n+1..2n are copy 2. For a disk this is the lattice sphere \
<psi_0|psi_0>. The surface is closed, so P has an eigenvalue exactly 1.";

PinnedLoopMass::usage =
  "PinnedLoopMass[P] gives -Log[Det[1 - P]] with the first site deleted (killing at one \
point). For a closed surface with zero mode, Det'[1 - P] = n Det[minor], so this equals \
-Log[Det'[1 - P]] + Log[n].";

CutEdges::usage =
  "CutEdges[A, B] gives the directed edges {a, b} with a in A, b in B and a, b \
nearest neighbours. CutEdges[B, A] gives the same edges in the opposite direction.";

ShowSites::usage =
  "ShowSites[{sites1, sites2, ...}] plots one or more regions. \
ShowSites[{sites1, ...}, edges] also draws the given edges, e.g. from CutEdges.";

Begin["`Private`"];

$nbrs = {{1, 0}, {-1, 0}, {0, 1}, {0, -1}};

RegionSites[pred_, {x0_, x1_}, {y0_, y1_}] :=
  Select[Tuples[{Range[x0, x1], Range[y0, y1]}], TrueQ[pred[#]] &];

(* bounding box around center c with half-width R *)
box[c_, R_] := Sequence[{Floor[c[[1]] - R], Ceiling[c[[1]] + R]},
                        {Floor[c[[2]] - R], Ceiling[c[[2]] + R]}];

Options[DiskSites] = {"Center" -> {0, 0}};
DiskSites[R_, OptionsPattern[]] := With[{c = OptionValue["Center"]},
  RegionSites[Total[(# - c)^2] < R^2 &, box[c, R]]];

Options[AnnulusSites] = {"Center" -> {0, 0}};
AnnulusSites[r_, R_, OptionsPattern[]] := With[{c = OptionValue["Center"]},
  RegionSites[r^2 <= Total[(# - c)^2] < R^2 &, box[c, R]]];

HoppingBlock[from_List, to_List] := Module[{idx, rules},
  idx = AssociationThread[to -> Range[Length[to]]];
  rules = Flatten[
    Table[
      With[{j = Lookup[idx, Key[from[[i]] + d], 0]},
        If[j == 0, Nothing, {i, j} -> 1/4]],
      {i, Length[from]}, {d, $nbrs}],
    1];
  SparseArray[rules, {Length[from], Length[to]}]];

TransitionMatrix[sites_List] := HoppingBlock[sites, sites];

GreensFunction[sites_List] :=
  Inverse[IdentityMatrix[Length[sites]] - N[Normal[TransitionMatrix[sites]]]];

(* P_D is symmetric, so use its real spectrum; avoids under/overflow of Det *)
LoopMass[sites_List] :=
  -Total[Log[1 - Eigenvalues[N[Normal[TransitionMatrix[sites]]]]]];

(* duplicate positions (sites with two missing neighbours) must add, so count them *)
GluedTransitionMatrix[sites_List] := Module[{n = Length[sites], idx, pos},
  idx = AssociationThread[sites -> Range[n]];
  pos = Flatten[
    Table[
      With[{j = Lookup[idx, Key[sites[[i]] + d], 0]},
        If[j == 0,
          {{i, i + n}, {i + n, i}},        (* cut edge -> twin site *)
          {{i, j}, {i + n, j + n}}]],      (* ordinary edge, both copies *)
      {i, n}, {d, $nbrs}],
    2];
  SparseArray[KeyValueMap[#1 -> #2/4 &, Counts[pos]], {2 n, 2 n}]];

PinnedLoopMass[P_] :=
  -Total[Log[Eigenvalues[N[IdentityMatrix[Length[P] - 1] - Normal[P[[2 ;;, 2 ;;]]]]]]];

CutEdges[A_List, B_List] := Module[{inB},
  inB = AssociationThread[B -> True];
  Flatten[
    Table[If[Lookup[inB, Key[a + d], False], {a, a + d}, Nothing],
      {a, A}, {d, $nbrs}],
    1]];

ShowSites[sets_List, edges_List : {}] := Show[
  ListPlot[sets, AspectRatio -> Automatic, PlotStyle -> PointSize[Medium],
    PlotLegends -> Automatic, Frame -> True, Axes -> False],
  Graphics[{Gray, Thick, Line /@ edges}]];

End[];
EndPackage[];
