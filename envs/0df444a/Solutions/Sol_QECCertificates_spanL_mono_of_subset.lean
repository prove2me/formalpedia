-- Prove2me | solution 1 for QECCertificates.spanL_mono_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:47:42.361818+00:00
-- url     : https://prove2.me/submissions/f12695c2-202b-4f47-93e1-570ffd13879b

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {A B : List (Vec n)} (h : A ⊆ B) : spanL A ≤ spanL B :=
  Submodule.span_mono fun _ hx => h hx
end QECCertificates
