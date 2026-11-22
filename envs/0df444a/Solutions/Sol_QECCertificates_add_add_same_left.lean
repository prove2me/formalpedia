-- Prove2me | solution 1 for QECCertificates.add_add_same_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:26.878457+00:00
-- url     : https://prove2.me/submissions/e80e734b-3a8a-4e82-ac38-9d74bc2bc779

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
theorem _root_.solution (v w : Vec n) : v + (v + w) = w := by
  rw [← add_assoc, add_self, zero_add]
end QECCertificates
