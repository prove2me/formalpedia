-- Prove2me | solution 1 for QECCertificates.isEchelon_rowReduce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:05:29.045221+00:00
-- url     : https://prove2.me/submissions/5dfe893c-dd4f-4440-9449-1762df424c8f

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Theorems.Thm_QECCertificates_readOff_nil
public import Theorems.Thm_QECCertificates_eq_zero_of_lt_leadIdx
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_isReduced_insertPivot
public import Theorems.Thm_QECCertificates_isReduced_nil
public import Theorems.Thm_QECCertificates_leadIdx_eq_one
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_reduceAgainst_apply_piv
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil


attribute [local simp] QECCertificates.readOff_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (L : List (Vec n)) : IsEchelon (rowReduce L) := by
  have key : ∀ (D : List (PivRow n)) (rest : List (Vec n)), IsEchelon D →
      IsEchelon (rowReduceFrom D rest) := by
    intro D rest
    induction rest generalizing D with
    | nil => intro h; exact h
    | cons v rest ih =>
        intro h
        rw [rowReduceFrom_cons]
        refine ih (D := step D v) ?_
        unfold step
        split
        · exact h
        · rename_i hw
          constructor
          · have hred := isReduced_insertPivot (D := D) (w := reduceAgainst D v)
              (p := leadIdx (reduceAgainst D v) hw) h.1
              (leadIdx_eq_one (reduceAgainst D v) hw) (reduceAgainst_apply_piv h.1 v)
            simpa [insertPivot] using hred
          · intro ri hri i hi
            rw [insertPivot] at hri
            rcases List.mem_append.mp hri with hmap | hsingle
            · obtain ⟨rk, hrk, rfl⟩ := List.mem_map.mp hmap
              change (rk.1 + (rk.1 (leadIdx (reduceAgainst D v) hw))
                • reduceAgainst D v) i = 0
              rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              rcases lt_trichotomy (leadIdx (reduceAgainst D v) hw) rk.2 with hlt | heq | hgt
              · rw [h.2 rk hrk _ hlt, zero_mul, add_zero, h.2 rk hrk i hi]
              · rw [heq, h.1.1 rk hrk, one_mul]
                have hi' : i < leadIdx (reduceAgainst D v) hw := by rw [heq]; exact hi
                rw [eq_zero_of_lt_leadIdx hw hi', h.2 rk hrk i hi, add_zero]
              · rw [eq_zero_of_lt_leadIdx hw (lt_of_lt_of_le hi hgt.le), mul_zero, add_zero,
                  h.2 rk hrk i hi]
            · have hrw : ri = (reduceAgainst D v, leadIdx (reduceAgainst D v) hw) := by
                simpa using hsingle
              rw [hrw] at hi ⊢
              exact eq_zero_of_lt_leadIdx hw hi
  exact key [] L ⟨isReduced_nil, by simp⟩
end QECCertificates
