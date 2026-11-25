-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.evl_cs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:18:39.945037+00:00
-- url     : https://prove2.me/submissions/3b59965f-d047-4d5e-ad6b-683a9d4cd729

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open scoped ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {ι : Type*} (s : Finset ι) (u a : ι → ℂ) :
    ‖∑ i ∈ s, conj (u i) * a i‖ ^ 2 ≤ (∑ i ∈ s, ‖u i‖ ^ 2) * ∑ i ∈ s, ‖a i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, conj (u i) * a i‖ ≤ ∑ i ∈ s, ‖u i‖ * ‖a i‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_mul, Complex.norm_conj]
  calc ‖∑ i ∈ s, conj (u i) * a i‖ ^ 2 ≤ (∑ i ∈ s, ‖u i‖ * ‖a i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq s _ _
end ReciprocityTheory.L2DbarEstimates.I
