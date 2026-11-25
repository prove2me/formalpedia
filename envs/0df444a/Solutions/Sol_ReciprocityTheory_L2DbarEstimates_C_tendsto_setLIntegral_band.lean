-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.tendsto_setLIntegral_band
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:29.324841+00:00
-- url     : https://prove2.me/submissions/7be930fb-537c-4457-a5a0-ca6db6c9db68

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCut
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeak
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeak
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_measurableSet_ge_of_continuousOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {W : Set (V n)} (hW : IsOpen W) {f : V n → ℝ}
    (hf : ContinuousOn f W) {φ : V n → ℝ≥0∞} (hφ : ∫⁻ z in W, φ z < ⊤) :
    Tendsto (fun k : ℕ => ∫⁻ z in {z | z ∈ W ∧ (k : ℝ) + 1 ≤ f z}, φ z) atTop (𝓝 0) := by
  set A : ℕ → Set (V n) := fun k => {z | z ∈ W ∧ (k : ℝ) + 1 ≤ f z} with hA
  have hmeas : ∀ k, MeasurableSet (A k) := fun k => measurableSet_ge_of_continuousOn hW hf _
  have hanti : Antitone A := by
    intro i j hij z hz
    refine ⟨hz.1, le_trans ?_ hz.2⟩
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have hempty : (⋂ k, A k) = ∅ := by
    ext z
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨k, hk⟩ := exists_nat_gt (f z)
    exact ⟨k, fun h => by have := h.2; linarith⟩
  have hfin : ∃ k, volume.withDensity φ (A k) ≠ ⊤ := ⟨0, by
    rw [withDensity_apply _ (hmeas 0)]
    exact (lt_of_le_of_lt (lintegral_mono_set (fun z hz => hz.1)) hφ).ne⟩
  have h := tendsto_measure_iInter_atTop (fun k => (hmeas k).nullMeasurableSet) hanti hfin
  rw [hempty, measure_empty] at h
  refine h.congr (fun k => ?_)
  simp only [Function.comp_apply]
  exact withDensity_apply _ (hmeas k)
end ReciprocityTheory.L2DbarEstimates.C
