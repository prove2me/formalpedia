-- Prove2me | solution 1 for QECCertificates.EchSelf_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:51.240802+00:00
-- url     : https://prove2.me/submissions/a540445f-c412-4a48-bd7a-c4e3a2a576ca

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
theorem _root_.solution (D : List (PivRow n)) (x : PivRow n) (hD : EchSelf D)
    (hx : x.1 x.2 = 1) : EchSelf (D ++ [x]) := by
  intro i
  rw [List.get_eq_getElem]
  by_cases h : (i : ℕ) < D.length
  · rw [List.getElem_append_left h]
    simpa [List.get_eq_getElem] using hD ⟨i.val, h⟩
  · have hlast : (D ++ [x])[(i : ℕ)] = x := by
      rw [List.getElem_append_right (by omega : D.length ≤ (i : ℕ))]
      simp [show (i : ℕ) - D.length = 0 from by
        have := length_append_singleton D x; omega]
    rw [hlast]
    exact hx
end QECCertificates
