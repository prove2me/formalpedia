-- Prove2me | solution 1 for QECCertificates.lightVecs_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:49:38.331112+00:00
-- url     : https://prove2.me/submissions/b15b1936-05aa-47a9-a71a-825c775440a1

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (n : ℕ) : lightVecs n 0 = [0] := by
  cases n with
  | zero => rw [lightVecs.eq_1]
  | succ n => rw [lightVecs.eq_2]
end QECCertificates
