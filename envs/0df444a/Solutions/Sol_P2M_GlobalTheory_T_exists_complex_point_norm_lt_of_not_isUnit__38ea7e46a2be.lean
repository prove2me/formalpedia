-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_complex_point_norm_lt_of_not_isUnit__38ea7e46a2be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:59:13.027429+00:00
-- url     : https://prove2.me/submissions/603b55e7-9685-4b14-96d8-36f5d125bac2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComplexPointNormLtOfNotIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComplexPointNormLtOfNotIsUnitStatement
import Theorems.Thm_GlobalTheory_exists_complex_point_norm_lt_of_not_isUnit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K B : Type) [Field K] [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B] (σ : K →+* ℂ) (n : ℕ) (w : Fin n → B) (u q : B), ¬ IsUnit u → q ≠ 0 → ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ φ : B →+* ℂ, φ.comp (algebraMap K B) = σ ∧ φ q ≠ 0 ∧ ‖φ u‖ < ε ∧ ∀ i, ‖φ (w i)‖ ≤ M := by
  first | exact @GlobalTheory.exists_complex_point_norm_lt_of_not_isUnit | exact GlobalTheory.exists_complex_point_norm_lt_of_not_isUnit | (intros; apply GlobalTheory.exists_complex_point_norm_lt_of_not_isUnit <;> assumption)
end _root_.GlobalTheory.T
