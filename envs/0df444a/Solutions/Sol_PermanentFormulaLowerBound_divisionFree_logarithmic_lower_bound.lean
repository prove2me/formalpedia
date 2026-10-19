-- Prove2me | solution 1 for PermanentFormulaLowerBound.divisionFree_logarithmic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/6dcc0bce-2adf-49e6-a54c-6dd7fec15ad9

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
    (hbound : n ^ 4 ≤ 32 * (2 * Nat.clog 2 n) * leaves) :
    (n : ℝ) ^ 4 / (128 * Real.logb 2 (n : ℝ)) ≤ (leaves : ℝ) := by
  convert fourth_power_logarithmic_lower_bound hn
    (by norm_num : 0 < 32) hbound using 1
  norm_num
end PermanentFormulaLowerBound
