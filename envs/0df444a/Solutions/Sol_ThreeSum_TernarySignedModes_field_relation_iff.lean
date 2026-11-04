-- Prove2me | solution 1 for ThreeSum.TernarySignedModes.field_relation_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:44:05.096977+00:00
-- url     : https://prove2.me/submissions/7cba7265-725a-4986-a45e-8e7ad5a0cf82

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Theorems.Thm_ThreeSum_TernarySignedModes_requesterRaw_abs
import Theorems.Thm_ThreeSum_TernarySignedModes_rawMode_abs
import Theorems.Thm_ThreeSum_TernarySignedModes_intCast_bounded_injective
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset
namespace ThreeSum.TernarySignedModes
theorem _root_.solution {p U radix J : ℕ} (hb : 1 < radix) (hp : 2*radix<p)
    (a b c : ℤ) (carry : CarryWord J) :
    (∀ k, fieldLeft p U radix J b k+fieldRight p U radix J c k=
      fieldRequester p U radix J a carry k) ↔
    (∀ k, leftRaw U radix J b k+rightRaw U radix J c k=requesterRaw U radix J a carry k) := by
  constructor
  · intro h k
    apply intCast_bounded_injective hp (rawMode_abs hb b c k) (requesterRaw_abs hb a carry k)
    simpa only [rawMode,Int.cast_add,fieldLeft,fieldRight,fieldRequester] using h k
  · intro h k
    simpa only [Int.cast_add,fieldLeft,fieldRight,fieldRequester] using
      congrArg (fun x : ℤ => (x : ZMod p)) (h k)
end ThreeSum.TernarySignedModes
