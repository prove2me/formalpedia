-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.iteratedFDeriv_eq_zero_of_isBigO_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:41:37.163032+00:00
-- url     : https://prove2.me/submissions/4a7ac7df-daae-45df-b24e-c545c5c6bb53

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Lemmata_CharacterDirections_Cdir
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fderiv_isBigO_of_isBigO_pow
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
    ContDiffOn ℂ ∞ f U → (f =O[𝓝 x] fun v => ‖v - x‖ ^ (m + 1)) →
    ∀ k ≤ m, iteratedFDeriv ℂ k f x = 0 := by
  induction m with
  | zero =>
    intro F _ _ f U x hU hx hf hO k hk
    obtain rfl : k = 0 := by omega
    rw [← norm_eq_zero, norm_iteratedFDeriv_zero, norm_eq_zero]
    exact hO.eq_zero_of_norm_pow (by omega)
  | succ m ih =>
    intro F _ _ f U x hU hx hf hO k hk
    rcases k with _ | k
    · rw [← norm_eq_zero, norm_iteratedFDeriv_zero, norm_eq_zero]
      exact hO.eq_zero_of_norm_pow (by omega)
    · have hd : ContDiffOn ℂ ∞ (fderiv ℂ f) U := hf.fderiv_of_isOpen hU top_add_one_le_top
      have hO' := fderiv_isBigO_of_isBigO_pow hU hx (hf.differentiableOn top_ne_zero_withTop) hO
      rw [← norm_eq_zero, ← norm_iteratedFDeriv_fderiv, norm_eq_zero]
      exact ih (fderiv ℂ f) U x hU hx hd hO' k (by omega)
end ReciprocityTheory.L2DbarEstimates.Y
