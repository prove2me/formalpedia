-- Prove2me | solution 1 for QECCertificates.spanL_append_eq_of_add_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:00.38528+00:00
-- url     : https://prove2.me/submissions/d1c4ac90-7041-4779-9fc5-c96d8c5dde51

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_spanL_append_singleton
public import Theorems.Thm_QECCertificates_spanL_mono_of_subset
public import Theorems.Thm_QECCertificates_mem_spanL_append_singleton_of_add_mem
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.add_self

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {A : List (Vec n)} {v w : Vec n}
    (h : v + w ∈ spanL A) : spanL (A ++ [w]) = spanL (A ++ [v]) := by
  have hwv : w ∈ spanL (A ++ [v]) := mem_spanL_append_singleton_of_add_mem h
  have hvw : v ∈ spanL (A ++ [w]) :=
    mem_spanL_append_singleton_of_add_mem (A := A) (v := w) (w := v)
      (by simpa [add_comm] using h)
  refine le_antisymm ?_ ?_
  · rw [spanL_append_singleton]
    refine sup_le (spanL_mono_of_subset (by intro x hx; simp [hx])) ?_
    exact Submodule.span_le.2 fun x hx => by
      have hx' : x = w := by simpa using hx
      rw [hx']; exact hwv
  · rw [spanL_append_singleton]
    refine sup_le (spanL_mono_of_subset (by intro x hx; simp [hx])) ?_
    exact Submodule.span_le.2 fun x hx => by
      have hx' : x = v := by simpa using hx
      rw [hx']; exact hvw
end QECCertificates
