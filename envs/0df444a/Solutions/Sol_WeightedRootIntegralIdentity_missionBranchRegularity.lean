-- Prove2me | solution 1 for WeightedRootIntegralIdentity.missionBranchRegularity
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T10:50:12.507207+00:00
-- url     : https://prove2.me/submissions/7c2028e6-2181-4d66-b60a-b856b28b814d

import Mathlib

theorem solution
    (F : ℂ → ℂ) (D : Set ℂ)
    (hF : DifferentiableOn ℂ F D) :
    ContinuousOn F D := by
  exact hF.continuousOn
