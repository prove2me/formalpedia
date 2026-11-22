-- Prove2me | solution 1 for QECCertificates.mem_spanL_append_singleton_of_add_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:24.087934+00:00
-- url     : https://prove2.me/submissions/38a1aa8c-d8f8-454b-b2f2-8ad764fbd5f3

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_subset_spanL
public import Theorems.Thm_QECCertificates_spanL_mono_of_subset
public import Theorems.Thm_QECCertificates_add_add_left_cancel
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
    (h : v + w ∈ spanL A) : w ∈ spanL (A ++ [v]) := by
  have hv : v ∈ spanL (A ++ [v]) := subset_spanL (by simp)
  have hu : v + w ∈ spanL (A ++ [v]) := spanL_mono_of_subset (by intro x hx; simp [hx]) h
  have key : (v + w) + v = w := add_add_left_cancel v w
  exact key ▸ Submodule.add_mem _ hu hv
end QECCertificates
