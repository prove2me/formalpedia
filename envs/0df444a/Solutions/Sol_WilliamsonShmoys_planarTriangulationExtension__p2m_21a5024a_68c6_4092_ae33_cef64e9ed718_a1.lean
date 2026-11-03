-- Prove2me | solution 1 for WilliamsonShmoys.planarTriangulationExtension__p2m_21a5024a_68c6_4092_ae33_cef64e9ed718_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:04:03.225867+00:00
-- url     : https://prove2.me/submissions/65de0797-321e-4cc6-9d56-cdc23bc8d251

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingMaximalExtension__p2m_0ab193fe_0f8a_4383_a58d_9f4c1a7627f8_a3
import Theorems.Thm_WilliamsonShmoys_maximalPlanarExtensionCardinality__p2m_0ab193fe_0f8a_4383_a58d_9f4c1a7627f8_a3

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      HasPlanarDrawingOn M ∧
      (letI : DecidableRel L.Adj := dL
       letI : DecidableRel M.Adj := dM
       L.edgeFinset ⊆ M.edgeFinset) ∧
      (letI : DecidableRel M.Adj := dM
       M.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨M, dM, hM, hLM, hmax⟩ :=
    WilliamsonShmoys.planarDrawingMaximalExtension__p2m_0ab193fe_0f8a_4383_a58d_9f4c1a7627f8_a3
      L dL hL hn
  exact ⟨M, dM, hM, hLM,
    WilliamsonShmoys.maximalPlanarExtensionCardinality__p2m_0ab193fe_0f8a_4383_a58d_9f4c1a7627f8_a3
      M dM hM hmax hn⟩