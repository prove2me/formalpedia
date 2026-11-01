-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_2a4e0817_5ede_4993_80da_c0938cce21b3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:59:40.700358+00:00
-- url     : https://prove2.me/submissions/30c62835-07f9-4fa0-bb77-6047d22b85e2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_exists__p2m_afb5df26_e4fb_4772_9aa3_0e4304c46b48_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_of_card_ge_three__p2m_afb5df26_e4fb_4772_9aa3_0e4304c46b48_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧ L ≤ M ∧
        M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hMplanar, hLM, hMmax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_afb5df26_e4fb_4772_9aa3_0e4304c46b48_a1
      L hplanar
  refine ⟨M, hMplanar, hLM, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count_of_card_ge_three__p2m_afb5df26_e4fb_4772_9aa3_0e4304c46b48_a1
    M hMplanar hMmax hcard