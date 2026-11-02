-- Prove2me | solution 1 for WilliamsonShmoys.finite_drawable_maximal_extension__p2m_5d7adedc_405a_4aa7_a840_9d1b809cbdd4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:43:22.294378+00:00
-- url     : https://prove2.me/submissions/7d7a7fc0-bc9a-4ae3-8e14-acac10306000

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_drawable_edge_maximizer__p2m_0117d7a7_55cc_4763_b339_05a114946f12_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V,
          M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by
  classical
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.finite_drawable_edge_maximizer__p2m_0117d7a7_55cc_4763_b339_05a114946f12_a2
      L hL
  refine ⟨M, hLM, hM, ?_⟩
  intro N hMN hN
  have heq : M.edgeSet = N.edgeSet :=
    Set.eq_of_subset_of_ncard_le (SimpleGraph.edgeSet_mono hMN) (hmax N hMN hN)
  have hsubset : N.edgeSet ⊆ M.edgeSet := by rw [heq]
  exact SimpleGraph.edgeSet_subset_edgeSet.mp hsubset