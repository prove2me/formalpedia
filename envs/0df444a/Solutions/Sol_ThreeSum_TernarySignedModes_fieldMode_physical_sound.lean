-- Prove2me | solution 1 for ThreeSum.TernarySignedModes.fieldMode_physical_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:44:06.222538+00:00
-- url     : https://prove2.me/submissions/f091b7ef-e861-4bab-b3f0-cd5778379a12

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Theorems.Thm_ThreeSum_TernarySignedModes_rawMode_abs
import Theorems.Thm_ThreeSum_TernarySignedModes_intCast_bounded_injective
import Theorems.Thm_ThreeSum_TernarySignedModes_rawMode_physical_sound

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset
namespace ThreeSum.TernarySignedModes
theorem _root_.solution {p U radix J : ℕ} {b c b' c' : ℤ}
    (hb : 1 < radix) (hp : 2*radix<p)
    (hB : |b| ≤ (U : ℤ)) (hC : |c| ≤ (U : ℤ))
    (hB' : |b'| ≤ (U : ℤ)) (hC' : |c'| ≤ (U : ℤ))
    (hcap : 4*U<radix^J)
    (hmode : ∀ k, fieldMode p U radix J b c k=fieldMode p U radix J b' c' k) :
    c-b=c'-b' := by
  apply rawMode_physical_sound hB hC hB' hC' hcap
  intro k
  exact intCast_bounded_injective hp (rawMode_abs hb b c k) (rawMode_abs hb b' c' k) (hmode k)
end ThreeSum.TernarySignedModes
