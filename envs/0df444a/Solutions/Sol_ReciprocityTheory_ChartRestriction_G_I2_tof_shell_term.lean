-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.tof_shell_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:23:29.099253+00:00
-- url     : https://prove2.me/submissions/3ae5e4ac-e116-449a-9504-689299160267

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofFinrankIRLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_key


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
theorem _root_.solution (d k : ℕ) (hd : 2 ≤ d) :
    (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) ≤
      (3 * (d : ℝ)) ^ d * (Real.exp (-1) * Real.exp (1 - Real.pi / 2) ^ k) := by
  have hpi := Real.pi_gt_three
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hE : Real.exp (-1) * Real.exp (1 - Real.pi / 2) ^ k =
      Real.exp (-1 + k * (1 - Real.pi / 2)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
  rw [hE]
  have key : (3 * ((k : ℝ) + 1)) ^ d ≤
      (3 * (d : ℝ)) ^ d * Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2))) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · subst hk0
      have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have hdd : (4 : ℝ) ≤ (d : ℝ) ^ d := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ (d : ℝ) ^ 2 := by gcongr
          _ ≤ (d : ℝ) ^ d := pow_le_pow_right₀ (by linarith) hd
      have hQ : Real.pi / 2 * ((0 : ℕ) : ℝ) ^ 2 + (-1 + ((0 : ℕ) : ℝ) * (1 - Real.pi / 2)) = -1 := by
        simp
      rw [hQ, Real.exp_neg]
      have h1 : (1 : ℝ) ≤ (d : ℝ) ^ d * (Real.exp 1)⁻¹ := by
        rw [le_mul_inv_iff₀ (Real.exp_pos 1)]
        linarith
      calc (3 * (((0 : ℕ) : ℝ) + 1)) ^ d = 3 ^ d * 1 := by simp
        _ ≤ 3 ^ d * ((d : ℝ) ^ d * (Real.exp 1)⁻¹) := by gcongr
        _ = (3 * (d : ℝ)) ^ d * (Real.exp 1)⁻¹ := by rw [mul_pow]; ring
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      by_cases hkd : k + 1 ≤ d
      · have hkd' : (k : ℝ) + 1 ≤ d := by exact_mod_cast hkd
        have h1 : (3 * ((k : ℝ) + 1)) ^ d ≤ (3 * (d : ℝ)) ^ d :=
          pow_le_pow_left₀ (by positivity) (by linarith) d
        have h2 : 0 ≤ Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2)) := by
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ Real.pi / 2)
            (by linarith : (0 : ℝ) ≤ k)) (by linarith : (0 : ℝ) ≤ k - 1)]
        calc (3 * ((k : ℝ) + 1)) ^ d ≤ (3 * (d : ℝ)) ^ d := h1
          _ ≤ _ := le_mul_of_one_le_right (by positivity) (Real.one_le_exp h2)
      · have hdk : (d : ℝ) ≤ k := by exact_mod_cast (by omega : d ≤ k)
        have hk2 : (2 : ℝ) ≤ k := le_trans hd' hdk
        have h1 : ((k : ℝ) + 1) ^ d ≤ Real.exp ((k : ℝ) * k) := by
          calc ((k : ℝ) + 1) ^ d ≤ (Real.exp k) ^ d :=
                pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (k : ℝ)]) d
            _ = Real.exp (d * k) := by rw [← Real.exp_nat_mul]
            _ ≤ Real.exp (k * k) := Real.exp_le_exp.mpr (by nlinarith)
        have h2 : (k : ℝ) * k ≤ Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2)) := by
          have hkk : 2 ≤ (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
          have hpp : (1 : ℝ) / 2 ≤ Real.pi / 2 - 1 := by linarith
          nlinarith [mul_le_mul hpp hkk (by norm_num) (by linarith)]
        have h3 : (1 : ℝ) ≤ (d : ℝ) ^ d := one_le_pow₀ (by linarith)
        calc (3 * ((k : ℝ) + 1)) ^ d = 3 ^ d * ((k : ℝ) + 1) ^ d := mul_pow _ _ _
          _ ≤ 3 ^ d * Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2))) := by
            gcongr
            exact h1.trans (Real.exp_le_exp.mpr h2)
          _ ≤ 3 ^ d * ((d : ℝ) ^ d *
              Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2)))) := by
            gcongr
            exact le_mul_of_one_le_left (Real.exp_pos _).le h3
          _ = _ := by rw [mul_pow]; ring
  have hexp : Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2))) *
      Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) = Real.exp (-1 + k * (1 - Real.pi / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc _ ≤ (3 * (d : ℝ)) ^ d * Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2))) *
        Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right key (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, hexp]
end ReciprocityTheory.ChartRestriction.G.I2
