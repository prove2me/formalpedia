-- Prove2me | solution 1 for QECCertificates.add_eq_zero_iff_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:18.57461+00:00
-- url     : https://prove2.me/submissions/4c0759f1-40bb-4bfd-8ac5-af3ab92148f2

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
theorem _root_.solution (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    rw [← CharTwo.add_self_eq_zero b] at h
    exact add_right_cancel_iff.mp h
  · intro h
    rw [h, CharTwo.add_self_eq_zero]
end QECCertificates
