-- Prove2me | solution 1 for QECCertificates.addSmul_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:42:46.584361+00:00
-- url     : https://prove2.me/submissions/2b7f4522-f924-4036-8d8c-8053e4491377

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_add_self
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.add_self

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (v r : Vec n) (c : ZMod 2) (i : Fin n) :
    addSmul v r c i = v i + c * r i := by
  simp [addSmul, Pi.add_apply, Pi.smul_apply]
end QECCertificates
