-- Prove2me | solution 1 for QECCertificates.reduceAgainst_get_piv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:02.421417+00:00
-- url     : https://prove2.me/submissions/1112eb4e-c959-424c-89ec-b6e71b07f2a3

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_EchSelf_tail
public import Theorems.Thm_QECCertificates_EchPair_tail
public import Theorems.Thm_QECCertificates_EchPair_head_rows
public import Theorems.Thm_QECCertificates_IsReduced_tail
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_reduceAgainst_cons
public import Theorems.Thm_QECCertificates_reduceAgainst_eq_zero_of_rows_zero
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
theorem _root_.solution {D : List (PivRow n)} (v : Vec n) (h1 : EchSelf D)
    (h2 : EchPair D) : ∀ i : Fin D.length, (reduceAgainst D v) (D.get i).2 = 0 := by
  induction D generalizing v with
  | nil => intro i; exact i.elim0
  | cons r D ih =>
      rw [reduceAgainst_cons]
      intro i
      revert i
      refine Fin.cases ?_ ?_
      · simp only [List.get_cons_zero]
        refine reduceAgainst_eq_zero_of_rows_zero (hrows := h2.head_rows) ?_
        have hr : r.1 r.2 = 1 := by
          have hh := h1 (0 : Fin (D.length + 1))
          simpa [List.get_cons_zero] using hh
        rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hr, mul_one]
        exact CharTwo.add_self_eq_zero (v r.2)
      · simp only [List.get_cons_succ']
        exact ih _ h1.tail h2.tail
end QECCertificates
