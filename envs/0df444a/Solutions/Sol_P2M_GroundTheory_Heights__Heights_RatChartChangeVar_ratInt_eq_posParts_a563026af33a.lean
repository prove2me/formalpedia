-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratInt_eq_posParts_a563026af33a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:35.02448+00:00
-- url     : https://prove2.me/submissions/93c52468-43cc-4e59-b02d-fcc06d25e629

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatChartChangeVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSheetNoRatNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatChartChangeVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratDens_eq_posParts_46417a6351ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratPosDens_nonneg_662d6e890f87
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatChartChangeVar_measurable_ratPosDens_6e6772a3a708

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets
open GroundTheory.Heights₂.Heights.RatChartChangeVar
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.RatChartChangeVar
theorem _root_.solution (hM : RatSheetSumMeasurable.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ}
    (hfin : ∀ y, (RatChart.ratFibre J p q y).Finite) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) :
    (Integrable (RatChart.ratAbsDens J p q f φ) ↔
      (∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y)) +
        ∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q (-f) φ y) < ⊤) ∧
    (Integrable (RatChart.ratAbsDens J p q f φ) → ∫ y, RatChart.ratDens J p q f φ y =
      (∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y)).toReal -
        (∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q (-f) φ y)).toReal) := by
  have h0 := ratPosDens_nonneg J p q f φ
  have h1 := ratPosDens_nonneg J p q (-f) φ
  have m0 := measurable_ratPosDens hM hfin hf φ
  have m1 := measurable_ratPosDens hM hfin hf.neg φ
  have habs : RatChart.ratAbsDens J p q f φ =
      fun y => RatChart.ratPosDens J p q f φ y + RatChart.ratPosDens J p q (-f) φ y :=
    funext fun y => (ratDens_eq_posParts f φ y (hfin y)).1
  have hlin : ∫⁻ y, ENNReal.ofReal (RatChart.ratAbsDens J p q f φ y) =
      (∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y)) +
        ∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q (-f) φ y) := by
    rw [habs, ← lintegral_add_left m0.ennreal_ofReal]
    exact lintegral_congr fun y => ENNReal.ofReal_add (h0 y) (h1 y)
  have hint : Integrable (RatChart.ratAbsDens J p q f φ) ↔
      ∫⁻ y, ENNReal.ofReal (RatChart.ratAbsDens J p q f φ y) < ⊤ := by
    rw [habs, Integrable, hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun y => add_nonneg (h0 y) (h1 y))]
    exact and_iff_right (m0.add m1).aestronglyMeasurable
  refine ⟨hint.trans (by rw [hlin]), fun hi => ?_⟩
  have hi0 : Integrable (RatChart.ratPosDens J p q f φ) := hi.mono' m0.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (h0 y), habs]; linarith [h1 y])
  have hi1 : Integrable (RatChart.ratPosDens J p q (-f) φ) := hi.mono' m1.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (h1 y), habs]; linarith [h0 y])
  have hd : RatChart.ratDens J p q f φ =
      fun y => RatChart.ratPosDens J p q f φ y - RatChart.ratPosDens J p q (-f) φ y :=
    funext fun y => (ratDens_eq_posParts f φ y (hfin y)).2
  rw [hd, integral_sub hi0 hi1,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) m0.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h1) m1.aestronglyMeasurable]
end GroundTheory.Heights₂.Heights.RatChartChangeVar
