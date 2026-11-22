-- Prove2me | solution 1 for QECCertificates.spanL_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:39.034317+00:00
-- url     : https://prove2.me/submissions/94153524-4f85-4859-8da7-3367f8ab202e

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
theorem _root_.solution : spanL ([] : List (Vec n)) = ⊥ := by
  have h : {x : Vec n | x ∈ ([] : List (Vec n))} = ∅ := by
    ext x; simp
  rw [spanL, h, Submodule.span_empty]
end QECCertificates
