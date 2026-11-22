-- Prove2me | solution 1 for QECCertificates.kerL_eq_of_spanL_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:40.052799+00:00
-- url     : https://prove2.me/submissions/c8a0c2da-97b7-4af5-ac70-6b0c6cefddf7

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
public import Theorems.Thm_QECCertificates_subset_spanL
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil


attribute [local simp] QECCertificates.mem_kerL

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {A B : List (Vec n)} (h : spanL A = spanL B) : kerL A = kerL B := by
  have key : ∀ {P Q : List (Vec n)}, spanL P ≤ spanL Q → kerL Q ≤ kerL P := by
    intro P Q hPQ x hx
    rw [mem_kerL] at hx ⊢
    intro p hp
    exact Submodule.span_induction
      (fun y hy => hx y hy) (by simp)
      (fun u v _ _ ihu ihv => by rw [add_dotProduct, ihu, ihv, add_zero])
      (fun c u _ ihu => by rw [smul_dotProduct, ihu, smul_zero])
      (hPQ (subset_spanL hp))
  exact le_antisymm (key h.ge) (key h.le)
end QECCertificates
