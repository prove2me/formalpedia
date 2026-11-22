-- Prove2me | solution 1 for QECCertificates.spanL_ofFn_eq_span_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:46.086314+00:00
-- url     : https://prove2.me/submissions/585abf3a-5ad0-4e28-9e73-e4be13e0b6ce

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
theorem _root_.solution {m : ℕ} (f : Fin m → Vec n) :
    spanL (List.ofFn f) = Submodule.span (ZMod 2) (Set.range f) := by
  rw [spanL]
  congr 1
  ext x
  change x ∈ List.ofFn f ↔ x ∈ Set.range f
  rw [List.mem_ofFn, Set.mem_range]
end QECCertificates
