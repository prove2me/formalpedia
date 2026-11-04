-- Prove2me | solution 1 for ThreeSum.TernarySignedReduction.original_difference_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:43:45.657043+00:00
-- url     : https://prove2.me/submissions/2ffe9938-6a57-436c-a4d3-8e445c41a6fd

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Theorems.Thm_ThreeSum_TernarySignedReduction_shiftOne_lt
import Theorems.Thm_ThreeSum_TernarySignedReduction_shiftTwo_lt
import Theorems.Thm_ThreeSum_TernarySignedReduction_shifted_addition_iff
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
import Theorems.Thm_ThreeSum_TernarySignedReduction_tagged_relation_iff
import Theorems.Thm_ThreeSum_TernarySignedDigits_addition_iff_carry
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero


attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset
namespace ThreeSum.TernarySignedReduction
theorem _root_.solution {U radix J : ℕ} {a b c : ℤ}
    (ha : |a| ≤ (U : ℤ)) (hb : |b| ≤ (U : ℤ)) (hc : |c| ≤ (U : ℤ))
    (hcap : 4*U<radix^J) :
    c-b=a ↔ ∃ carry ∈ carryCatalog J,
      ∀ k, leftRaw U radix J b k+rightRaw U radix J c k=requesterRaw U radix J a carry k := by
  rw [← shifted_addition_iff ha hb hc,
    addition_iff_carry (shiftOne_lt hb hcap) (shiftOne_lt ha hcap) (shiftTwo_lt hc hcap)]
  constructor
  · rintro ⟨carry,hv,hd⟩
    exact ⟨carry,mem_carryCatalog _ |>.mpr hv,(tagged_relation_iff _ _ _ _ _ _ _).mpr hd⟩
  · rintro ⟨carry,hv,hd⟩
    exact ⟨carry,mem_carryCatalog _ |>.mp hv,(tagged_relation_iff _ _ _ _ _ _ _).mp hd⟩
end ThreeSum.TernarySignedReduction
