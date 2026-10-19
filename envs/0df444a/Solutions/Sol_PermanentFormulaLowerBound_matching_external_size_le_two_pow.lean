-- Prove2me | solution 1 for PermanentFormulaLowerBound.matching_external_size_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/a8a77a20-87fc-4d91-9f66-0a88cc7ebc78

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {n : ℕ} :
    n - 2 * Nat.clog 2 n ≤ 2 ^ Nat.clog 2 n :=
  (Nat.sub_le n _).trans (Nat.le_pow_clog (by norm_num) n)
end PermanentFormulaLowerBound
