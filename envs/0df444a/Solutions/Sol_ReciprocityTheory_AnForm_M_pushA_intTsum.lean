-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pushA_intTsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:49.3682+00:00
-- url     : https://prove2.me/submissions/4b68367d-1dd7-4669-a4b9-02ef1e1ac8e4

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : ℕ → α → ℝ}
    (hF : ∀ i, Integrable (F i) μ) (hsum : ∀ a, Summable fun i => F i a)
    (hs : Summable fun i => ∫ a, ‖F i a‖ ∂μ) : Integrable (fun a => ∑' i, F i a) μ := by
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
    (fun N => (integrable_finsetSum (Finset.range N) fun i _ => hF i).aestronglyMeasurable)
    (Eventually.of_forall fun a => (hsum a).hasSum.tendsto_sum_nat), ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ :=
        lintegral_mono fun a => enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ := lintegral_tsum fun i => (hF i).aestronglyMeasurable.enorm
    _ = ∑' i, ENNReal.ofReal (∫ a, ‖F i a‖ ∂μ) := by
        congr 1; funext i; rw [ofReal_integral_norm_eq_lintegral_enorm (hF i)]
    _ = ENNReal.ofReal (∑' i, ∫ a, ‖F i a‖ ∂μ) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun a => norm_nonneg _) hs).symm
    _ < ⊤ := ENNReal.ofReal_lt_top
end ReciprocityTheory.AnForm.M
