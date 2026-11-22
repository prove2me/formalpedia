-- Prove2me | solution 1 for QECCertificates.EchPair.head_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:14.678273+00:00
-- url     : https://prove2.me/submissions/88225488-2ece-40ed-97ac-986d74127232

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
theorem _root_.solution {r : PivRow n} {D : List (PivRow n)} (h : EchPair (r :: D)) :
    ∀ r' ∈ D, r'.1 r.2 = 0 := by
  intro r' hr'
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hr'
  have hlt : (0 : Fin (D.length + 1)) < i.succ := by simp
  have hh := h 0 i.succ hlt
  rw [List.get_cons_zero, List.get_cons_succ'] at hh
  rw [← hi]
  exact hh
end EchPair
end QECCertificates
