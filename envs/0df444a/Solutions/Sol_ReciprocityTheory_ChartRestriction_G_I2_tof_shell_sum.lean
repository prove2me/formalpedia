-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.tof_shell_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:40:07.531331+00:00
-- url     : https://prove2.me/submissions/fcd09d81-af7b-4cc1-af53-29d991283516

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofFinrankIRLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_shell_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (d K : ℕ) (hd : 2 ≤ d) :
    ∑ k ∈ Finset.range K, (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) ≤
      2 * (3 * (d : ℝ)) ^ d := by
  set r := Real.exp (1 - Real.pi / 2) with hr
  have hpi := Real.pi_gt_three
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r ≤ 2 / 3 := by
    have h := Real.add_one_le_exp (Real.pi / 2 - 1)
    have hrr : r * Real.exp (Real.pi / 2 - 1) = 1 := by
      rw [hr, ← Real.exp_add]
      simp
    nlinarith
  have he1 : Real.exp (-1) ≤ 1 / 2 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    have hrr : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]
      simp
    have := Real.exp_pos (-1)
    nlinarith
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range K, r ^ k := Finset.sum_nonneg (fun k _ => pow_nonneg hr0.le k)
  have hS : ∑ k ∈ Finset.range K, r ^ k ≤ 3 := by
    have h := geom_sum_mul r K
    have : 0 ≤ r ^ K := by positivity
    nlinarith
  have hd0 : (0 : ℝ) ≤ (3 * (d : ℝ)) ^ d := by positivity
  calc ∑ k ∈ Finset.range K, (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2)
      ≤ ∑ k ∈ Finset.range K, (3 * (d : ℝ)) ^ d * (Real.exp (-1) * r ^ k) :=
        Finset.sum_le_sum (fun k _ => tof_shell_term d k hd)
    _ = (3 * (d : ℝ)) ^ d * Real.exp (-1) * ∑ k ∈ Finset.range K, r ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring
    _ ≤ (3 * (d : ℝ)) ^ d * (1 / 2) * 3 := by gcongr
    _ ≤ 2 * (3 * (d : ℝ)) ^ d := by nlinarith
end ReciprocityTheory.ChartRestriction.G.I2
