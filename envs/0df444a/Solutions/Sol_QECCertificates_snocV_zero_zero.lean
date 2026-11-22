-- Prove2me | solution 1 for QECCertificates.snocV_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:43:04.092481+00:00
-- url     : https://prove2.me/submissions/1361704e-7707-4be7-9435-ce9df63a4cd0

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution : snocV (0 : Vec n) (0 : ZMod 2) = 0 := by
  funext i
  by_cases h : (i : ℕ) < n
  · rw [snocV, dif_pos h]; rfl
  · rw [snocV, dif_neg h]; rfl
end QECCertificates
