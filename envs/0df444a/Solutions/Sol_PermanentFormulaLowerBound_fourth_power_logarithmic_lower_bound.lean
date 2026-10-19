-- Prove2me | solution 1 for PermanentFormulaLowerBound.fourth_power_logarithmic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/ee13a978-7d45-4727-9faf-16bd23b4acae

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_clog_two_cast_le_two_mul_logb

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n leaves c : ℕ} (hn : 32 ≤ n) (hc : 0 < c)
    (hbound : n ^ 4 ≤ c * (2 * Nat.clog 2 n) * leaves) :
    (n : ℝ) ^ 4 /
        (4 * (c : ℝ) * Real.logb 2 (n : ℝ)) ≤ (leaves : ℝ) := by
  have hlog : 0 < Real.logb 2 (n : ℝ) := by
    apply Real.logb_pos (by norm_num)
    exact_mod_cast (by omega : 1 < n)
  have hclog := clog_two_cast_le_two_mul_logb (by omega : 2 ≤ n)
  have hclog' :
      2 * (Nat.clog 2 n : ℝ) ≤ 4 * Real.logb 2 (n : ℝ) := by
    linarith
  have hbound' :
      (n : ℝ) ^ 4 ≤
        (c : ℝ) * (2 * (Nat.clog 2 n : ℝ)) * (leaves : ℝ) := by
    exact_mod_cast hbound
  have hdenom : 0 < 4 * (c : ℝ) * Real.logb 2 (n : ℝ) := by
    positivity
  apply (div_le_iff₀ hdenom).2
  calc
    (n : ℝ) ^ 4 ≤
        (c : ℝ) * (2 * (Nat.clog 2 n : ℝ)) * (leaves : ℝ) := hbound'
    _ ≤ (c : ℝ) * (4 * Real.logb 2 (n : ℝ)) * (leaves : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hclog' (by positivity)) (by positivity)
    _ = (leaves : ℝ) *
        (4 * (c : ℝ) * Real.logb 2 (n : ℝ)) := by ring
end PermanentFormulaLowerBound
