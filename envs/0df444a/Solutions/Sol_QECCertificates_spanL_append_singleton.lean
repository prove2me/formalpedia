-- Prove2me | solution 1 for QECCertificates.spanL_append_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:23.650807+00:00
-- url     : https://prove2.me/submissions/6a8935ff-8fb9-4a39-a866-b12a03a59474

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Theorems.Thm_QECCertificates_spanL_append
public import Theorems.Thm_QECCertificates_spanL_singleton

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (A : List (Vec n)) (v : Vec n) :
    spanL (A ++ [v]) = spanL A ⊔ Submodule.span (ZMod 2) ({v} : Set (Vec n)) := by
  rw [spanL_append, spanL_singleton]
end QECCertificates
