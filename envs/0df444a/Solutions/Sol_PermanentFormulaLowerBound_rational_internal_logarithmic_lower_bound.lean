-- Prove2me | solution 1 for PermanentFormulaLowerBound.rational_internal_logarithmic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/6afe8687-1d09-4b45-b2e6-ded4734c1ad7

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_fourth_power_logarithmic_lower_bound
import Theorems.Thm_PermanentFormulaLowerBound_two_le_leaves_of_fourth_power_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n leaves gates : ℕ} (hn : 32 ≤ n)
    (htree : leaves = gates + 1)
    (hbound : n ^ 4 ≤ 48 * (2 * Nat.clog 2 n) * leaves) :
    (n : ℝ) ^ 4 / (384 * Real.logb 2 (n : ℝ)) ≤ (gates : ℝ) := by
  have hleaves : 2 ≤ leaves :=
    two_le_leaves_of_fourth_power_bound hn (by norm_num : 48 ≤ 48) hbound
  have htwice : leaves ≤ 2 * gates := by omega
  have hgate :
      n ^ 4 ≤ 96 * (2 * Nat.clog 2 n) * gates := by
    calc
      n ^ 4 ≤ 48 * (2 * Nat.clog 2 n) * leaves := hbound
      _ ≤ 48 * (2 * Nat.clog 2 n) * (2 * gates) :=
        Nat.mul_le_mul_left (48 * (2 * Nat.clog 2 n)) htwice
      _ = 96 * (2 * Nat.clog 2 n) * gates := by ring
  convert fourth_power_logarithmic_lower_bound hn
    (by norm_num : 0 < 96) hgate using 1
  norm_num
end PermanentFormulaLowerBound
