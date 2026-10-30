-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_3fe6515b_8335_4a72_a208_f1a2ec6f6eaf
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:14:55.914319+00:00
-- url     : https://prove2.me/submissions/6a7ca258-cd34-44be-9a2a-c41026de2eba

import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_extension_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hmax : WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by
  obtain ⟨J, hsub, hJ, hcount⟩ :=
    WilliamsonShmoys.exists_triangulated_planar_extension_edge_count H hmax.1 hV
  have hEq : J.edgeSet = H.edgeSet := hmax.2 J hsub hJ
  rw [← hEq]
  omega