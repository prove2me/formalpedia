-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.shell_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:07.652779+00:00
-- url     : https://prove2.me/submissions/88108ad6-2d6e-4aa9-b818-cd12ffe34f27

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ShellCeilEq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal


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
theorem _root_.solution (C : ℝ) (hC : 0 ≤ C) (k : ℕ) :
    ENNReal.ofReal (Real.exp (-(Real.log (1 + C) + k))) * ENNReal.ofReal C ≤
      ENNReal.ofReal (Real.exp (-(k : ℝ))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log (by linarith)]
  have h1 : 0 < 1 + C := by linarith
  have h2 := Real.exp_pos (-(k : ℝ))
  have h3 : (1 + C)⁻¹ * C ≤ 1 := by
    rw [inv_mul_le_iff₀ h1]
    linarith
  have h4 : 0 ≤ (1 + C)⁻¹ := inv_nonneg.mpr h1.le
  nlinarith [mul_le_mul_of_nonneg_left h3 h2.le]
end ReciprocityTheory.L2DbarEstimates.F
