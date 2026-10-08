-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootReplaceAbstractBankAndResidue
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T06:57:47.530516+00:00
-- url     : https://prove2.me/submissions/376a232c-16bc-4be6-8066-2df79dfe661d

import Mathlib

theorem solution
    (A R : ℂ) (J S P : ℝ)
    (hbalance : A - starRingEnd ℂ A = R)
    (hjump : A - starRingEnd ℂ A = 2 * Complex.I * (J : ℂ))
    (hres : R = 2 * Real.pi * Complex.I * ((S - P : ℝ) : ℂ)) :
    J / Real.pi = S - P := by
  have h : 2 * Complex.I * (J : ℂ) =
      2 * Real.pi * Complex.I * ((S - P : ℝ) : ℂ) := by
    rw [← hjump, hbalance, hres]
  have him := congrArg Complex.im h
  norm_num at him
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]
  nlinarith [him]
