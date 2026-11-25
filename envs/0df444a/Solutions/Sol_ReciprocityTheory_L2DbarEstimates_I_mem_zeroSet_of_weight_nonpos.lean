-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.mem_zeroSet_of_weight_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:16:17.048003+00:00
-- url     : https://prove2.me/submissions/4f3bd025-951c-4241-8e6a-1122118ebee5

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocalExtensionEqMulJacobian
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_weightFunction_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ)
    (hr : r ≠ 0) (x : M) (h : ev n g ph r x ≤ 0) : x ∈ zeroSet n g := by
  have h0 : ev n g ph r x = 0 := le_antisymm h (weightFunction_nonneg n g ph r x)
  unfold ev at h0
  have hs : (∑ i, ‖g i x‖ ^ 2) = 0 := by
    rcases div_eq_zero_iff.1 h0 with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact h2
      · exact absurd h2 (Real.exp_pos _).ne'
    · exact absurd h1 (pow_ne_zero 2 hr)
  intro i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖g i x‖)).1 hs i (Finset.mem_univ i)
  simpa using this
end ReciprocityTheory.L2DbarEstimates.I
