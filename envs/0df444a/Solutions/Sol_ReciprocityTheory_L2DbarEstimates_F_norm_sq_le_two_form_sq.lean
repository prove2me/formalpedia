-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.norm_sq_le_two_form_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:13:53.290861+00:00
-- url     : https://prove2.me/submissions/9134839a-ee7f-4af8-8e61-86f24222a9a2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Cutoff

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
theorem _root_.solution (n : ℕ) (σx : Fin n → Fin n → ℂ) : ‖σx‖ ^ 2 ≤ 2 * sq2 n σx := by
  set S := ∑ j, ∑ k, ‖σx j k‖ ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have h1 : ‖σx‖ ≤ Real.sqrt S := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun k => ?_
    apply (Real.le_sqrt (norm_nonneg _) hS0).mpr
    calc ‖σx j k‖ ^ 2 ≤ ∑ k', ‖σx j k'‖ ^ 2 :=
          Finset.single_le_sum (f := fun k' => ‖σx j k'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)
      _ ≤ S := Finset.single_le_sum (f := fun j' => ∑ k', ‖σx j' k'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ j)
  have h2 : 2 * sq2 n σx = S := by
    unfold sq2
    ring
  rw [h2]
  calc ‖σx‖ ^ 2 ≤ (Real.sqrt S) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = S := Real.sq_sqrt hS0
end ReciprocityTheory.L2DbarEstimates.F
