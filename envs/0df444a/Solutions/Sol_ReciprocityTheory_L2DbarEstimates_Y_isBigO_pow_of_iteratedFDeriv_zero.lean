-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.isBigO_pow_of_iteratedFDeriv_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:33.368814+00:00
-- url     : https://prove2.me/submissions/74d01d40-b38b-412d-b226-678d1f23daab

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Lemmata_CharacterDirections_Cdir
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isBigO_succ_of_fderiv_isBigO
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_top_ne_zero_withTop
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_top_add_one_le_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics Metric Set
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} (m : ℕ) : ∀ {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (f : V n → F) (U : Set (V n)) (x : V n), IsOpen U → x ∈ U →
    ContDiffOn ℂ ∞ f U → (∀ k < m, iteratedFDeriv ℂ k f x = 0) →
    f =O[𝓝 x] fun v => ‖v - x‖ ^ m := by
  induction m with
  | zero =>
    intro F _ _ f U x hU hx hf _
    simp only [pow_zero]
    exact (hf.continuousOn.continuousAt (hU.mem_nhds hx)).tendsto.isBigO_one ℝ
  | succ m ih =>
    intro F _ _ f U x hU hx hf h
    have h0 : f x = 0 := by
      have := h 0 (by omega)
      rwa [← norm_eq_zero, norm_iteratedFDeriv_zero, norm_eq_zero] at this
    have hd : ContDiffOn ℂ ∞ (fderiv ℂ f) U := hf.fderiv_of_isOpen hU top_add_one_le_top
    have hO := ih (fderiv ℂ f) U x hU hx hd (fun k hk => by
      rw [← norm_eq_zero, norm_iteratedFDeriv_fderiv, norm_eq_zero]
      exact h (k + 1) (by omega))
    exact isBigO_succ_of_fderiv_isBigO hU hx (hf.differentiableOn top_ne_zero_withTop) h0 hO
end ReciprocityTheory.L2DbarEstimates.Y
