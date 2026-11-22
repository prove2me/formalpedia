-- Prove2me | solution 1 for QECCertificates.spanL_rowList_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:01.206799+00:00
-- url     : https://prove2.me/submissions/52d8465d-74bc-4b86-8ce4-728eab34cfbb

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Theorems.Thm_QECCertificates_add_reduceAgainst_mem
public import Theorems.Thm_QECCertificates_spanL_rowList_insertPivot
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_spanL_append_eq_of_add_mem
public import Theorems.Thm_QECCertificates_spanL_append_singleton
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
theorem _root_.solution (D : List (PivRow n)) (v : Vec n) :
    spanL (rowList (step D v)) = spanL (rowList D ++ [v]) := by
  unfold step
  split
  · rename_i hw
    have hv : v ∈ spanL (rowList D) := by
      have h := add_reduceAgainst_mem D v
      rw [hw, add_zero] at h
      exact h
    have hsup : Submodule.span (ZMod 2) ({v} : Set (Vec n)) ≤ spanL (rowList D) :=
      Submodule.span_le.2 fun x hx => by
        have hx' : x = v := by simpa using hx
        rw [hx']; exact hv
    rw [spanL_append_singleton, sup_eq_left.mpr hsup]
  · rename_i hw
    rw [spanL_rowList_insertPivot]
    exact spanL_append_eq_of_add_mem (add_reduceAgainst_mem D v)
end QECCertificates
