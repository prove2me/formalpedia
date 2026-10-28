-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_equations_2138cef4_5572_4c93_aec0_4104f419c27b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:30:31.277995+00:00
-- url     : https://prove2.me/submissions/5cb7a3c5-917b-47f3-aa41-3d38eb74a08a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_via_faces
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_via_triangulation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet ⊆ K.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      (Fintype.card V + f = K.edgeSet.ncard + 2) ∧
      (3 * f = 2 * K.edgeSet.ncard) := by
  have hUpper :=
    WilliamsonShmoys.planar_edge_count_upper_bound_via_faces K hK hV
  have hLower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound_via_triangulation
      K hK hmax hV
  have hE : K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
    Nat.le_antisymm hUpper hLower
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega