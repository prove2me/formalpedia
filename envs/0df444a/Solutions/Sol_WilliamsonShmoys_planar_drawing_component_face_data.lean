-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_component_face_data
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:26:49.214279+00:00
-- url     : https://prove2.me/submissions/37429211-660a-4a69-8f66-5452cb5decb9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_component_face_data_of_local_edge_bounds
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_induced_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ parts : Finset (Finset V),
      (∀ C ∈ parts, C.Nonempty) ∧
      (∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D) ∧
      parts.biUnion id = Finset.univ ∧
      G.edgeSet.ncard = ∑ C ∈ parts, (G.induce (fun v => v ∈ C)).edgeSet.ncard ∧
      (∀ C ∈ parts,
        (G.induce (fun v => v ∈ C)).Connected ∧
        (if 3 ≤ C.card then
          ∃ f : ℕ,
            C.card + f = (G.induce (fun v => v ∈ C)).edgeSet.ncard + 2 ∧
            3 * f ≤ 2 * (G.induce (fun v => v ∈ C)).edgeSet.ncard
        else
          (G.induce (fun v => v ∈ C)).edgeSet.ncard ≤ 3 * C.card - 3)) := by
  apply WilliamsonShmoys.planar_drawing_component_face_data_of_local_edge_bounds
  intro C hC hconn hcard
  exact WilliamsonShmoys.planar_drawing_connected_induced_edge_bound
    G hG C hconn hcard