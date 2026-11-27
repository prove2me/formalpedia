-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_field_of_isIntegral_image__4fafb0d6e24d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:52:24.520871+00:00
-- url     : https://prove2.me/submissions/ca6dccb4-7c4c-4fbf-8aa0-e858ea13e149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFieldOfIsIntegralImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFieldOfIsIntegralImageStatement
import Theorems.Thm_GlobalTheory_exists_field_of_isIntegral_image


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∃ (F : Type) (_ : Field F) (_ : CharZero F) (φ' : R →+* F), (∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ' r = n * x) ∧ ∀ (A : Type) [CommRing A] [Algebra ℚ A] (χ : R →+* A), (∀ r, φ r = 0 → χ r = 0) → ∃ χ' : F →+* A, χ'.comp φ' = χ := by
  first | exact @GlobalTheory.exists_field_of_isIntegral_image | exact GlobalTheory.exists_field_of_isIntegral_image | (intros; apply GlobalTheory.exists_field_of_isIntegral_image <;> assumption)
end _root_.GlobalTheory.T
