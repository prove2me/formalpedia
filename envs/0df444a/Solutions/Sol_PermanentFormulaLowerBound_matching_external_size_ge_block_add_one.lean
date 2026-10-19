-- Prove2me | solution 1 for PermanentFormulaLowerBound.matching_external_size_ge_block_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/f062bda7-69ba-47b0-982c-da9f2952c8f9

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_four_mul_clog_two_lt_self

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {n : ℕ} (hn : 32 ≤ n) :
    2 * Nat.clog 2 n + 1 ≤ n - 2 * Nat.clog 2 n := by
  have h := four_mul_clog_two_lt_self hn
  omega
end PermanentFormulaLowerBound
