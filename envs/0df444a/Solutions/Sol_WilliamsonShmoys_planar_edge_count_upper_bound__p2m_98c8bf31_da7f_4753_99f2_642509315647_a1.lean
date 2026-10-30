-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_98c8bf31_da7f_4753_99f2_642509315647_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:03:11.956116+00:00
-- url     : https://prove2.me/submissions/7d643e77-bc21-4e2f-929b-b26fc4fcd203
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_side_bound__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
import Lean.Elab.Tactic.Omega

open WilliamsonShmoys

set_option autoImplicit false

/-
Reduction using the actual topological faces of the supplied drawing.
The two Open children are independent geometric facts: the exact Euler
formula (including disconnected components and face finiteness), and
the edge-side budget when there are at least two edges.

The two-edge cutoff is essential: one edge and an isolated vertex have
one face, so 3f ≤ 2e fails despite having three vertices. Those small-edge
cases are discharged directly below. Bridges count twice in the side
budget; disconnected faces may have several boundary components.

Written arguments:
https://www.isibang.ac.in/~d.yogesh/Course_Notes/DM1/Ch13.S1.html
(Theorem 13.5, the disconnected Euler formula);
https://www.sp18.eecs70.org/static/notes/n5.html
(Planar Graphs, the two-edge cutoff and the double counting of sides).
No geometric child is claimed proved by this reduction.
-/

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  classical
  by_cases hsmall : G.edgeSet.ncard ≤ 1
  · omega
  · rcases hG with ⟨p, arc, hp, ha, hi⟩
    obtain ⟨hfaces, hEuler⟩ :=
      WilliamsonShmoys.planar_drawing_euler_formula__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9 G p arc hp ha hi
    have hE : 2 ≤ G.edgeSet.ncard := by omega
    have hSides :=
      WilliamsonShmoys.planar_drawing_face_side_bound__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
        G p arc hp ha hi hfaces hE
    have hpos : 0 < Fintype.card V := by omega
    letI : Nonempty V := Fintype.card_pos_iff.mp hpos
    have hcomponents : 0 < Nat.card G.ConnectedComponent := Nat.card_pos
    omega