-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.shell_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:28:46.265084+00:00
-- url     : https://prove2.me/submissions/a4aa4eda-aa0b-461f-b434-b2bba62f76a6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ShellCeilEq

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
theorem _root_.solution (a t : ℝ) (ht : a + 1 < t) :
    a + 1 + (⌈t - a - 2⌉₊ : ℝ) < t ∧ t ≤ a + 2 + (⌈t - a - 2⌉₊ : ℝ) := by
  constructor
  · rcases le_or_gt 0 (t - a - 2) with h | h
    · have := Nat.ceil_lt_add_one h
      linarith
    · rw [Nat.ceil_eq_zero.mpr h.le]
      simp only [CharP.cast_eq_zero, add_zero]
      linarith
  · have := Nat.le_ceil (t - a - 2)
    linarith
end ReciprocityTheory.L2DbarEstimates.F
