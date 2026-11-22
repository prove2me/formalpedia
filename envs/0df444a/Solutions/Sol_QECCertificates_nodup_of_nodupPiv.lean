-- Prove2me | solution 1 for QECCertificates.nodup_of_nodupPiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:35.912796+00:00
-- url     : https://prove2.me/submissions/916ab423-477c-486f-bea2-802cb13fcb43

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Theorems.Thm_QECCertificates_IsReduced_tail
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
open _root_.Matrix
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (D : List (PivRow n)) :
    IsReduced D → NodupPiv D → D.Nodup := by
  induction D with
  | nil => intro _ _; simp
  | cons r D ih =>
      intro hred h
      rw [List.nodup_cons]
      have hmap : (D.map (·.2)).Nodup := by
        have hh : ((r :: D).map (·.2)).Nodup := h
        rw [List.map_cons, List.nodup_cons] at hh
        exact hh.2
      refine ⟨?_, ih hred.tail hmap⟩
      intro hmem
      have hh : ((r :: D).map (·.2)).Nodup := h
      rw [List.map_cons, List.nodup_cons] at hh
      exact hh.1 (List.mem_map_of_mem hmem)
end QECCertificates
