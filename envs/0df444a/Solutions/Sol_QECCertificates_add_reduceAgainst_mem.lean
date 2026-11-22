-- Prove2me | solution 1 for QECCertificates.add_reduceAgainst_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:39.308965+00:00
-- url     : https://prove2.me/submissions/a51e5327-04d6-4d80-ac80-e846462ba323

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Theorems.Thm_QECCertificates_reduceAgainst_cons
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_add_same_right
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_spanL_mono_of_subset
public import Theorems.Thm_QECCertificates_subset_spanL
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
    v + reduceAgainst D v ∈ spanL (rowList D) := by
  induction D generalizing v with
  | nil => simp
  | cons r D ih =>
      rw [reduceAgainst_cons]
      have hr : r.1 ∈ spanL (rowList (r :: D)) := subset_spanL (by simp)
      have hih : (v + (v r.2) • r.1) + reduceAgainst D (v + (v r.2) • r.1) ∈ spanL (rowList D) :=
        ih _
      have hih' : (v + (v r.2) • r.1) + reduceAgainst D (v + (v r.2) • r.1)
          ∈ spanL (rowList (r :: D)) :=
        spanL_mono_of_subset (by intro x hx; exact List.mem_cons_of_mem r.1 hx) hih
      have hmem := Submodule.add_mem _ (Submodule.smul_mem _ (v r.2) hr) hih'
      have key : v + reduceAgainst D (v + (v r.2) • r.1)
          = (v r.2) • r.1 + ((v + (v r.2) • r.1) + reduceAgainst D (v + (v r.2) • r.1)) := by
        rw [← add_assoc]
        congr 1
        exact (add_add_same_right ((v r.2) • r.1) v).symm
      rw [key]
      exact hmem
end QECCertificates
