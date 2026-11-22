-- Prove2me | solution 1 for QECCertificates.mem_kerBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:46:29.743023+00:00
-- url     : https://prove2.me/submissions/30cea491-8027-4f6b-aabd-f05a7031245c

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
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
theorem _root_.solution {D : List (PivRow n)} {x : Vec n} :
    x ∈ kerBasis D ↔ ∃ j, j ∉ pivCols D ∧ kerVec D j = x := by
  simp only [kerBasis, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, of_decide_eq_true hj, rfl⟩
  · rintro ⟨j, hjp, rfl⟩
    exact ⟨j, decide_eq_true hjp, rfl⟩
end QECCertificates
