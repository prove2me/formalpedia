-- Prove2me | solution 1 for QECCertificates.reduceAgainst_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:44:20.825807+00:00
-- url     : https://prove2.me/submissions/cc296af6-627e-4e81-81bd-c9ef7b1c4bc5

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (ri : PivRow n) (D : List (PivRow n)) (v : Vec n) :
    reduceAgainst (ri :: D) v = reduceAgainst D (v + (v ri.2) • ri.1) := by
  simp [reduceAgainst, List.foldl_cons]
end QECCertificates
