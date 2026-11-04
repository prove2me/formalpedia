-- Prove2me | solution 1 for ThreeSum.TernarySignedModes.rawMode_physical_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:42:46.59434+00:00
-- url     : https://prove2.me/submissions/7711a44a-25b7-41b9-bda8-2b58fb9600fa

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedDigits_evaluate_digits_of_lt
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
import Theorems.Thm_ThreeSum_TernarySignedReduction_shiftOne_cast
import Theorems.Thm_ThreeSum_TernarySignedReduction_shiftOne_lt
import Theorems.Thm_ThreeSum_TernarySignedReduction_shiftTwo_cast
import Theorems.Thm_ThreeSum_TernarySignedReduction_shiftTwo_lt
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset
namespace ThreeSum.TernarySignedModes
theorem _root_.solution {U radix J : ℕ} {b c b' c' : ℤ}
    (hB : |b| ≤ (U : ℤ)) (hC : |c| ≤ (U : ℤ))
    (hB' : |b'| ≤ (U : ℤ)) (hC' : |c'| ≤ (U : ℤ))
    (hcap : 4*U<radix^J)
    (hmode : ∀ k, rawMode U radix J b c k=rawMode U radix J b' c' k) :
    c-b=c'-b' := by
  have hd : ∀ j ∈ range J,
      (digit radix (shiftTwo U c) j : ℤ)-(digit radix (shiftOne U b) j : ℤ)=
      (digit radix (shiftTwo U c') j : ℤ)-(digit radix (shiftOne U b') j : ℤ) := by
    intro j hj
    have h := hmode (.inl ⟨j,mem_range.mp hj⟩)
    simpa only [rawMode,leftRaw,rightRaw,sub_eq_add_neg,add_comm] using h
  have he := sum_congr rfl (fun j hj => congrArg (fun z : ℤ => z*(radix : ℤ)^j) (hd j hj))
  simp only [sub_mul,sum_sub_distrib] at he
  change evaluate radix J (fun j => (digit radix (shiftTwo U c) j : ℤ))-
      evaluate radix J (fun j => (digit radix (shiftOne U b) j : ℤ))=
    evaluate radix J (fun j => (digit radix (shiftTwo U c') j : ℤ))-
      evaluate radix J (fun j => (digit radix (shiftOne U b') j : ℤ)) at he
  rw [evaluate_digits_of_lt (shiftTwo_lt hC hcap),evaluate_digits_of_lt (shiftOne_lt hB hcap),
      evaluate_digits_of_lt (shiftTwo_lt hC' hcap),evaluate_digits_of_lt (shiftOne_lt hB' hcap)] at he
  rw [shiftTwo_cast hC,shiftOne_cast hB,shiftTwo_cast hC',shiftOne_cast hB'] at he
  omega
end ThreeSum.TernarySignedModes
