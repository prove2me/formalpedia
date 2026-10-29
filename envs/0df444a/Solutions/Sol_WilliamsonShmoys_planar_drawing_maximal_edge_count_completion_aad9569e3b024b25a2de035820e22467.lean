-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_edge_count_completion_aad9569e3b024b25a2de035820e22467
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:57:53.837997+00:00
-- url     : https://prove2.me/submissions/cfe9c609-7de2-4c6a-aa4f-be28c411fc64

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_by_finite_choice
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_has_euler_edge_count
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hKH, hH, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_by_finite_choice K hK
  refine ⟨H, hKH, hH, ?_⟩
  exact WilliamsonShmoys.maximal_planar_supergraph_has_euler_edge_count H hV hH hMax