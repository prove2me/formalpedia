-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paNum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:23:38.388855+00:00
-- url     : https://prove2.me/submissions/ae5259aa-d3bc-4272-ae95-96cb7a19c30f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (g : ℕ) (c R0 : ℝ) (hc : 0 ≤ c) (h270 : 270 ≤ R0 ^ 2)
    (h90 : 90 * ((g : ℝ) + c) ≤ R0 ^ 2) :
    2 ^ (1 + 3 * ((g : ℝ) + c) / 2) * (2 * 9 ^ g * Real.exp (-R0 ^ 2 / 16)) ≤ 1 / 2 := by
  have hl2 : Real.log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hy : 0 ≤ 1 + 3 * ((g : ℝ) + c) / 2 := by positivity
  have e1 : (2 : ℝ) ^ (1 + 3 * ((g : ℝ) + c) / 2) =
      Real.exp (Real.log 2 * (1 + 3 * ((g : ℝ) + c) / 2)) := Real.rpow_def_of_pos (by norm_num) _
  have e9 : (9 : ℝ) ^ g ≤ Real.exp (2.3 * g) := by
    rw [mul_comm, Real.exp_nat_mul]
    refine pow_le_pow_left₀ (by norm_num) ?_ g
    have h1 := Real.exp_one_gt_d9
    have h2 := Real.add_one_le_exp (0.3 : ℝ)
    have h3 : Real.exp 2.3 = Real.exp 1 * Real.exp 1 * Real.exp 0.3 := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    rw [h3]
    nlinarith
  have e2 : (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
  have key : (2 : ℝ) ^ (1 + 3 * ((g : ℝ) + c) / 2) * (2 * 9 ^ g * Real.exp (-R0 ^ 2 / 16)) ≤
      Real.exp (Real.log 2 * (1 + 3 * ((g : ℝ) + c) / 2) + (Real.log 2 + (2.3 * g + -R0 ^ 2 / 16))) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, e1, ← mul_assoc (Real.exp (Real.log 2))]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    exact mul_le_mul (le_of_eq e2) e9 (by positivity) (Real.exp_pos _).le
  refine key.trans ?_
  have hhalf : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [← hhalf]
  apply Real.exp_le_exp.2
  have hm : Real.log 2 * (1 + 3 * ((g : ℝ) + c) / 2) ≤ 0.7 * (1 + 3 * ((g : ℝ) + c) / 2) :=
    mul_le_mul_of_nonneg_right hl2.le hy
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  nlinarith
end ReciprocityTheory.ChartRestriction.G.I2
