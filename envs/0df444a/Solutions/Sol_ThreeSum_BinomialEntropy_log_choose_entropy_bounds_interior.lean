-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.log_choose_entropy_bounds_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:54:48.889582+00:00
-- url     : https://prove2.me/submissions/2570a0b6-4236-47ca-b2fa-a895031978d1

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Theorems.Thm_ThreeSum_BinomialEntropy_weight_bounds
import Theorems.Thm_ThreeSum_BinomialEntropy_weight_positive
import Theorems.Thm_ThreeSum_BinomialEntropy_log_weight
import Theorems.Thm_ThreeSum_BinomialEntropy_entropy_numerator

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.BinomialEntropy
open Finset Real Set Filter
open scoped Topology
set_option maxRecDepth 10000
namespace ThreeSum.BinomialEntropy
theorem _root_.solution {n k : ℕ} (hk0 : 0 < k) (hk : k < n) :
    (n : ℝ) * Real.binEntropy ((k : ℝ) / n) - Real.log (n + 1 : ℝ) ≤
        Real.log (n.choose k : ℝ) ∧
      Real.log (n.choose k : ℝ) ≤ (n : ℝ) * Real.binEntropy ((k : ℝ) / n) := by
  have hn : 0 < n := lt_trans hk0 hk
  have hw := weight_bounds hk
  have hup := Real.log_le_log (weight_positive hk0 hk) hw.1
  have hlo := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) ^ n) hw.2
  rw [Real.log_pow, log_weight hk0 hk] at hup
  rw [Real.log_pow, Real.log_mul (by positivity : (n + 1 : ℝ) ≠ 0)
    (weight_positive hk0 hk).ne', log_weight hk0 hk] at hlo
  rw [entropy_numerator hk0 hk]
  constructor <;> linarith
end ThreeSum.BinomialEntropy
