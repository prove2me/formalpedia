-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusionMaximalPlanarSupergraph__p2m_541725ce_ba0e_4ec7_9bf8_a3e758b67715_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:28:24.446852+00:00
-- url     : https://prove2.me/submissions/4f97d9e7-b8bf-447e-8923-bbaf09da3474

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finitePredicateHasInclusionMaximalSupergraph__p2m_58be6bd2_7b61_44ae_b8f6_153972a57451_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K) :
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj),
      K ≤ H ∧ HasPlanarDrawingOn H ∧
        ∀ (J : SimpleGraph V) (_ : DecidableRel J.Adj),
          H ≤ J → HasPlanarDrawingOn J → J ≤ H := by
  classical
  obtain ⟨H, hKH, hPlanarH, hmax⟩ :=
    WilliamsonShmoys.finitePredicateHasInclusionMaximalSupergraph__p2m_58be6bd2_7b61_44ae_b8f6_153972a57451_a1
      K HasPlanarDrawingOn hK
  exact ⟨H, inferInstance, hKH, hPlanarH, fun J _ hHJ hPlanarJ => hmax J hHJ hPlanarJ⟩