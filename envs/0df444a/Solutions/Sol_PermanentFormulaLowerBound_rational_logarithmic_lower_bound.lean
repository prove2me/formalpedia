-- Prove2me | solution 1 for PermanentFormulaLowerBound.rational_logarithmic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/d54df387-915b-403c-a98f-3cb0da145dcb

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_fourth_power_logarithmic_lower_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n leaves : ℕ} (hn : 32 ≤ n)
    (hbound : n ^ 4 ≤ 48 * (2 * Nat.clog 2 n) * leaves) :
    (n : ℝ) ^ 4 / (192 * Real.logb 2 (n : ℝ)) ≤ (leaves : ℝ) := by
  convert fourth_power_logarithmic_lower_bound hn
    (by norm_num : 0 < 48) hbound using 1
  norm_num
end PermanentFormulaLowerBound
