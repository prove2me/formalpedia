-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IntegralIndep_chartInt_eq_posParts_786379f5608c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:51:19.963214+00:00
-- url     : https://prove2.me/submissions/d8a57602-05b2-4631-93f9-331362b0e8fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_chartDens_eq_posParts_82c9e7e5e4bb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_chartPosDens_nonneg_e1523890f8fb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_measurable_chartPosDens_47c1c9528926

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.IntegralIndep
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.IntegralIndep
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) :
    (Integrable (chartAbsDens J A f φ) ↔
      (∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y)) +
        ∫⁻ y, ENNReal.ofReal (chartPosDens J A (-f) φ y) < ⊤) ∧
    (Integrable (chartAbsDens J A f φ) → chartInt J A f φ =
      (∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y)).toReal -
        (∫⁻ y, ENNReal.ofReal (chartPosDens J A (-f) φ y)).toReal) := by
  have h0 := chartPosDens_nonneg J A hA f φ
  have h1 := chartPosDens_nonneg J A hA (-f) φ
  have m0 := measurable_chartPosDens hA hf φ
  have m1 := measurable_chartPosDens hA hf.neg φ
  have habs : chartAbsDens J A f φ = fun y => chartPosDens J A f φ y + chartPosDens J A (-f) φ y :=
    funext fun y => (chartDens_eq_posParts hA f φ y).1
  have hlin : ∫⁻ y, ENNReal.ofReal (chartAbsDens J A f φ y) =
      (∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y)) +
        ∫⁻ y, ENNReal.ofReal (chartPosDens J A (-f) φ y) := by
    rw [habs, ← lintegral_add_left m0.ennreal_ofReal]
    exact lintegral_congr fun y => ENNReal.ofReal_add (h0 y) (h1 y)
  have hint : Integrable (chartAbsDens J A f φ) ↔
      ∫⁻ y, ENNReal.ofReal (chartAbsDens J A f φ y) < ⊤ := by
    rw [habs, Integrable, hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun y => add_nonneg (h0 y) (h1 y))]
    exact and_iff_right (m0.add m1).aestronglyMeasurable
  refine ⟨hint.trans (by rw [hlin]), fun hi => ?_⟩
  have hi0 : Integrable (chartPosDens J A f φ) := hi.mono' m0.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (h0 y), habs]; linarith [h1 y])
  have hi1 : Integrable (chartPosDens J A (-f) φ) := hi.mono' m1.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (h1 y), habs]; linarith [h0 y])
  have hd : chartDens J A f φ = fun y => chartPosDens J A f φ y - chartPosDens J A (-f) φ y :=
    funext fun y => (chartDens_eq_posParts hA f φ y).2
  rw [chartInt, hd, integral_sub hi0 hi1,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) m0.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h1) m1.aestronglyMeasurable]
end GroundTheory.Heights₂.Heights.IntegralIndep
