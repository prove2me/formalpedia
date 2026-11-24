-- Prove2me | solution 1 for TaoFivePrimes.euler_mascheroni_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T09:16:40.817198+00:00
-- url     : https://prove2.me/submissions/8a3693c0-4466-4543-bdaf-f7c577caaf21

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option maxRecDepth 100000

namespace TaoFivePrimes

/-- The exponential of the Euler–Mascheroni constant is less than `1.7857`. -/
theorem solution : Real.exp Real.eulerMascheroniConstant < 1.7857 := by
  have hγ : Real.eulerMascheroniConstant < (0.57855 : ℝ) := by
    have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 1024
    have h' : Real.eulerMascheroniSeq' 1024 = (harmonic 1024 : ℝ) - Real.log 1024 := by
      rw [Real.eulerMascheroniSeq', if_neg (by norm_num : (1024 : ℕ) ≠ 0)]
      norm_num
    rw [h'] at h
    have h3 : harmonic 1024 < (7.51 : ℚ) := by norm_num [harmonic]
    have h3R : (harmonic 1024 : ℝ) < 7.51 :=
      (Rat.cast_lt.mpr h3).trans_eq (by norm_num)
    have hlog : Real.log 1024 = 10 * Real.log 2 := by
      rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
      norm_num
    rw [hlog] at h
    nlinarith [Real.log_two_gt_d9]
  calc Real.exp Real.eulerMascheroniConstant
      < Real.exp (0.57855 : ℝ) := Real.exp_lt_exp.mpr hγ
    _ < 1.7857 := by
        have h := Real.exp_bound' (x := (0.57855 : ℝ)) (by norm_num) (by norm_num)
          (n := 6) (by norm_num)
        norm_num [Finset.sum_range_succ, Nat.factorial] at h
        linarith

end TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : Real.exp Real.eulerMascheroniConstant < 1.7857 :=
  TaoFivePrimes.solution
