-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratDens_eq_posParts_46417a6351ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:55.651873+00:00
-- url     : https://prove2.me/submissions/28b480ed-5a16-4642-a47c-5c7796e5b291

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatChartChangeVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSheetNoRatNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatChartChangeVar

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
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ)
    (hfin : (RatChart.ratFibre J p q y).Finite) :
    RatChart.ratAbsDens J p q f φ y = RatChart.ratPosDens J p q f φ y + RatChart.ratPosDens J p q (-f) φ y ∧
      RatChart.ratDens J p q f φ y = RatChart.ratPosDens J p q f φ y - RatChart.ratPosDens J p q (-f) φ y := by
  unfold RatChart.ratAbsDens RatChart.ratDens RatChart.ratPosDens RatChart.ratSheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine ⟨Finset.sum_congr rfl fun x _ => ?_, Finset.sum_congr rfl fun x _ => ?_⟩ <;>
    split_ifs <;> simp only [Pi.neg_apply, neg_mul, max_zero_add_max_neg_zero_eq_abs_self,
      max_zero_sub_max_neg_zero_eq_self, add_zero, sub_zero]
end GroundTheory.Heights₂.Heights.RatChartChangeVar
