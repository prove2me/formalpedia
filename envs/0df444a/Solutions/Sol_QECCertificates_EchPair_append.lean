-- Prove2me | solution 1 for QECCertificates.EchPair_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:51.762747+00:00
-- url     : https://prove2.me/submissions/b466129d-0f58-4252-88ea-dfdd7013bd8a

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
theorem _root_.solution (D : List (PivRow n)) (x : PivRow n) (hD : EchPair D)
    (hx : ∀ i : Fin D.length, x.1 (D.get i).2 = 0) : EchPair (D ++ [x]) := by
  intro i j hij
  simp only [List.get_eq_getElem]
  by_cases hj : (j : ℕ) < D.length
  · have hi : (i : ℕ) < D.length := by omega
    rw [List.getElem_append_left hj, List.getElem_append_left hi]
    exact hD ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
  · have hjlast : (D ++ [x])[(j : ℕ)] = x := by
      rw [List.getElem_append_right (by omega : D.length ≤ (j : ℕ))]
      simp [show (j : ℕ) - D.length = 0 from by
        have := length_append_singleton D x; omega]
    have hi : (i : ℕ) < D.length := by
      have := length_append_singleton D x; omega
    rw [hjlast, List.getElem_append_left hi]
    simpa [List.get_eq_getElem] using hx ⟨i.val, hi⟩
end QECCertificates
