-- Prove2me | solution 1 for ThreeSum.TernaryCarryCode.original_difference_code_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:50.304483+00:00
-- url     : https://prove2.me/submissions/a026133f-bfe3-48d0-b71f-2ac612d54d9f

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Theorems.Thm_ThreeSum_TernaryCarryCode_carryCatalog_eq_codes
import Theorems.Thm_ThreeSum_TernarySignedModes_original_difference_field_iff


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset
namespace ThreeSum.TernaryCarryCode
theorem _root_.solution {p U radix J : ℕ} {a b c : ℤ}
    (hb : 1<radix) (hp : 2*radix<p)
    (hA : |a|≤(U : ℤ)) (hB : |b|≤(U : ℤ)) (hC : |c|≤(U : ℤ))
    (hcap : 4*U<radix^J) :
    c-b=a ↔ ∃ q<2^J, digit 2 q 0=0 ∧
      ∀ k, TernarySignedModes.fieldLeft p U radix J b k+
        TernarySignedModes.fieldRight p U radix J c k=
        TernarySignedModes.fieldRequester p U radix J a (carryFromCode J q) k := by
  rw [TernarySignedModes.original_difference_field_iff hb hp hA hB hC hcap,
    carryCatalog_eq_codes]
  constructor
  · rintro ⟨carry,hcarry,hrel⟩
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hcarry
    exact ⟨q,mem_range.mp (mem_filter.mp hq).1,(mem_filter.mp hq).2,hrel⟩
  · rintro ⟨q,hq,hzero,hrel⟩
    exact ⟨carryFromCode J q,mem_image.mpr ⟨q,mem_filter.mpr ⟨mem_range.mpr hq,hzero⟩,rfl⟩,hrel⟩
end ThreeSum.TernaryCarryCode
