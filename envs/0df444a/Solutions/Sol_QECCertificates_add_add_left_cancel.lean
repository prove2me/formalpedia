-- Prove2me | solution 1 for QECCertificates.add_add_left_cancel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:01:47.837944+00:00
-- url     : https://prove2.me/submissions/ac4ba60a-07e8-403c-bc69-2557245d326a

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Theorems.Thm_QECCertificates_add_self
attribute [local simp] QECCertificates.add_self

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (v w : Vec n) : (v + w) + v = w := by
  rw [add_assoc, add_comm w v, ← add_assoc, add_self, zero_add]
end QECCertificates
