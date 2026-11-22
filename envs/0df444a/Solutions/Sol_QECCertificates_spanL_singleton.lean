-- Prove2me | solution 1 for QECCertificates.spanL_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:01:47.358803+00:00
-- url     : https://prove2.me/submissions/b6a670b9-a7c7-4069-b1db-158aaf44def9

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
theorem _root_.solution (v : Vec n) : spanL [v] = Submodule.span (ZMod 2) ({v} : Set (Vec n)) := by
  rw [spanL]
  congr 1
  ext x
  change x ∈ [v] ↔ x ∈ ({v} : Set (Vec n))
  simp
end QECCertificates
