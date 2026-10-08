-- Prove2me | solution 1 for WeightedRootIntegralIdentity.cpow_negative_real_boundary
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-13T14:54:26.010499+00:00
-- url     : https://prove2.me/submissions/67e15221-17d7-4c51-9ec2-df9616eae981

import Mathlib.Analysis.SpecialFunctions.Pow.Real
theorem solution (r w : ℝ) (hr : 0 ≤ r) :
    ((-(r : ℂ)) ^ (w : ℂ) = (Real.rpow r w : ℂ) * Complex.exp (((Real.pi * w : ℝ) : ℂ) * Complex.I)) ∧
    (starRingEnd ℂ ((-(r : ℂ)) ^ (w : ℂ)) = (Real.rpow r w : ℂ) * Complex.exp (-(((Real.pi * w : ℝ) : ℂ) * Complex.I))) := by
  have hupper : (-(r : ℂ)) ^ (w : ℂ) = (Real.rpow r w : ℂ) * Complex.exp (((Real.pi * w : ℝ) : ℂ) * Complex.I) := by
    have hneg : -(r : ℂ) = ((-r : ℝ) : ℂ) := by norm_num
    rw [hneg, Complex.ofReal_cpow_of_nonpos (neg_nonpos.mpr hr)]
    have hbase : -(((-r : ℝ) : ℂ)) = (r : ℂ) := by norm_num
    rw [hbase, ← Complex.ofReal_cpow hr]
    congr 2
    push_cast
    ring
  refine ⟨hupper, ?_⟩
  rw [hupper, map_mul]
  have hreal : starRingEnd ℂ (Real.rpow r w : ℂ) = (Real.rpow r w : ℂ) := by norm_num
  rw [hreal, ← Complex.exp_conj]
  congr 2
  simp
