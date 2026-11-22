-- Prove2me | solution 1 for QECCertificates.addSmul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:48.877808+00:00
-- url     : https://prove2.me/submissions/ede3887d-b5cb-4488-a7e2-8b788edc89d7

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_addSmul_apply
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.addSmul_apply

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (v r : Vec n) (c : ZMod 2) : addSmul v r c + c • r = v := by
  simp only [addSmul]
  rw [add_assoc, add_self, add_zero]
end QECCertificates
