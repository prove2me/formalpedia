-- Prove2me | solution 1 for ThreeSum.TernarySignedModes.original_difference_field_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:45:08.445315+00:00
-- url     : https://prove2.me/submissions/102a58e7-560b-485c-a400-147f3c7a26c4

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Theorems.Thm_ThreeSum_TernarySignedModes_field_relation_iff
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
import Theorems.Thm_ThreeSum_TernarySignedReduction_original_difference_iff
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset
namespace ThreeSum.TernarySignedModes
theorem _root_.solution {p U radix J : ℕ} {a b c : ℤ}
    (hb : 1 < radix) (hp : 2*radix<p)
    (ha : |a| ≤ (U : ℤ)) (hB : |b| ≤ (U : ℤ)) (hC : |c| ≤ (U : ℤ))
    (hcap : 4*U<radix^J) :
    c-b=a ↔ ∃ carry ∈ carryCatalog J,
      ∀ k, fieldLeft p U radix J b k+fieldRight p U radix J c k=
        fieldRequester p U radix J a carry k := by
  rw [original_difference_iff ha hB hC hcap]
  simp only [field_relation_iff hb hp]
end ThreeSum.TernarySignedModes
