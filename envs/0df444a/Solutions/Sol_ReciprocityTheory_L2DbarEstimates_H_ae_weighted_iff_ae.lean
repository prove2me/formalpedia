-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.ae_weighted_iff_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:09.69794+00:00
-- url     : https://prove2.me/submissions/1f18a4d3-7292-46fa-969b-98ad6fdba817

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_measurable_exp_neg_density
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) {ψ : M → ℝ}
    (hψ : Measurable ψ) (P : M → Prop) :
    (∀ᵐ x ∂wvol n z ψ, P x) ↔ ∀ᵐ x ∂vol n z, P x := by
  unfold wvol
  rw [ae_withDensity_iff (measurable_exp_neg_density hψ)]
  refine ⟨fun h => h.mono fun x hx => hx ?_, fun h => h.mono fun x hx _ => hx⟩
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
end ReciprocityTheory.L2DbarEstimates.H
