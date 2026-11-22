-- Prove2me | solution 1 for QECCertificates.EchPair.tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:14.162863+00:00
-- url     : https://prove2.me/submissions/5b1b77d7-ca41-4592-838a-f3665147d60b

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
namespace EchPair
theorem _root_.solution {r : PivRow n} {D : List (PivRow n)} (h : EchPair (r :: D)) : EchPair D := by
  intro i j hij
  have hh := h i.succ j.succ (by simpa using hij)
  simpa [List.get_cons_succ'] using hh
end EchPair
end QECCertificates
