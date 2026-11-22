-- Prove2me | solution 1 for QECCertificates.spanL_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:47:41.978805+00:00
-- url     : https://prove2.me/submissions/32a23716-959c-4658-aedf-10415b2164a2

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_add_self
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.add_self

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (A B : List (Vec n)) : spanL (A ++ B) = spanL A ⊔ spanL B := by
  have h : {x : Vec n | x ∈ A ++ B} = {x | x ∈ A} ∪ {x | x ∈ B} := by
    ext x; simp [List.mem_append]
  rw [spanL, h, Submodule.span_union]; rfl
end QECCertificates
