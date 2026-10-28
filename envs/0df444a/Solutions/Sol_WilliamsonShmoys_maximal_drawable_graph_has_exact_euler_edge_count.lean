-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_exact_euler_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:01:24.773797+00:00
-- url     : https://prove2.me/submissions/5ab1fb31-2fc3-499a-aadf-737739f89626
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_equations_2138cef4_5572_4c93_aec0_4104f419c27b

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet ⊆ K.edgeSet) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_equations_2138cef4_5572_4c93_aec0_4104f419c27b
      K hK hmax hV
  omega