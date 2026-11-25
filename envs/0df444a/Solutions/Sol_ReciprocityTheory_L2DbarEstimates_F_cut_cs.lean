-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_cs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:32:23.014724+00:00
-- url     : https://prove2.me/submissions/65931f2a-60fd-4881-93d8-53b90b6de536

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (a b : Fin n → ℂ) :
    ‖∑ j, a j * b j‖ ^ 2 ≤ (∑ j, ‖a j‖ ^ 2) * (∑ j, ‖b j‖ ^ 2) := by
  have h1 : ‖∑ j, a j * b j‖ ≤ ∑ j, ‖a j‖ * ‖b j‖ := by
    calc ‖∑ j, a j * b j‖ ≤ ∑ j, ‖a j * b j‖ := norm_sum_le _ _
      _ = ∑ j, ‖a j‖ * ‖b j‖ := Finset.sum_congr rfl fun j _ => norm_mul _ _
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun j => ‖b j‖)
  calc ‖∑ j, a j * b j‖ ^ 2 ≤ (∑ j, ‖a j‖ * ‖b j‖) ^ 2 := by
        first
        | exact pow_le_pow_left₀ (norm_nonneg _) h1 2
        | gcongr
    _ ≤ (∑ j, ‖a j‖ ^ 2) * (∑ j, ‖b j‖ ^ 2) := h2
end ReciprocityTheory.L2DbarEstimates.F
