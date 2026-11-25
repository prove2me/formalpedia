-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ConeToProjective_hypotheses_inhabited_93f353aa46af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:01:16.979306+00:00
-- url     : https://prove2.me/submissions/f44d2c13-27c5-4dad-b240-e20b71f9fdde

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isAffVariety_bot_ca242a8c4e80

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff ENNReal
noncomputable section
variable {n d e : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace ConeToProjective
theorem _root_.solution :
    IsAffVariety (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (1 + 1) ∧
      IsHomogIdeal (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      linForm (Pi.single (0 : Fin 2) (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      Measurable (fun _ : Fin 2 → ℂ => (1 : ℝ)) ∧
      (∀ c : ℂ, c ≠ 0 → ∀ y : Fin 2 → ℂ, (fun _ : Fin 2 → ℂ => (1 : ℝ)) (c • y) =
        (fun _ : Fin 2 → ℂ => (1 : ℝ)) y) := by
  refine ⟨isAffVariety_bot 2, ?_, ?_, measurable_const, fun _ _ _ => rfl⟩
  · intro f hf k
    rw [Ideal.mem_bot] at hf ⊢
    simp [hf]
  · rw [Ideal.mem_bot]
    simp [linForm, Pi.single_apply, X_ne_zero]
end ConeToProjective
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
