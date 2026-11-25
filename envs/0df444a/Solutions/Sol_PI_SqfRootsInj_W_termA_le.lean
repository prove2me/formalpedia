-- Prove2me | solution 1 for PI.SqfRootsInj.W.termA_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:40.230468+00:00
-- url     : https://prove2.me/submissions/f5001ddf-db9d-4612-8016-734429ffee6b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_SumSqPowLeTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_RpowQuarterPowFour
import Theorems.Thm_PI_SqfRootsInj_W_lp_pow_four_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution (g r e j ℓ : ℕ) (s : ℝ) (hs0 : 0 < s) (hs1 : 1 ≤ s) (hs4 : s ^ 4 = g)
    (hℓ : ℓ.Prime) (hB : ℓ ∉ BB r g) (he1 : 1 ≤ e) (her : e ≤ r) (hj : 2 * j ≤ e) :
    (((g ^ j - 1) * Lp g e ℓ * g ^ (r - e) : ℕ) : ℝ) ≤ (g : ℝ) ^ r * (s⁻¹) ^ e := by
  have hL : (Lp g e ℓ : ℝ) ≤ s ^ e := by
    have h4 : ((Lp g e ℓ : ℝ)) ^ 4 ≤ (s ^ e) ^ 4 := by
      rw [← pow_mul, mul_comm e 4, pow_mul, hs4]
      exact_mod_cast lp_pow_four_le hℓ hB he1 her
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h4
  have hgj : (g : ℝ) ^ j ≤ s ^ (2 * e) := by
    rw [← hs4, ← pow_mul]; exact pow_le_pow_right₀ hs1 (by omega)
  have hcast : (((g ^ j - 1) * Lp g e ℓ * g ^ (r - e) : ℕ) : ℝ) ≤
      (g : ℝ) ^ j * Lp g e ℓ * (g : ℝ) ^ (r - e) := by
    have : (g ^ j - 1) * Lp g e ℓ * g ^ (r - e) ≤ g ^ j * Lp g e ℓ * g ^ (r - e) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
    exact_mod_cast this
  have key : (g : ℝ) ^ r * (s⁻¹) ^ e = (g : ℝ) ^ (r - e) * s ^ (3 * e) := by
    have h1 : (g : ℝ) ^ r = (g : ℝ) ^ (r - e) * (s ^ 4) ^ e := by
      rw [hs4, ← pow_add]; congr 1; omega
    have h2 : s ^ e * (s⁻¹) ^ e = 1 := by rw [← mul_pow, mul_inv_cancel₀ hs0.ne', one_pow]
    rw [h1]
    calc (g : ℝ) ^ (r - e) * (s ^ 4) ^ e * (s⁻¹) ^ e
        = (g : ℝ) ^ (r - e) * s ^ (3 * e) * (s ^ e * (s⁻¹) ^ e) := by ring
      _ = _ := by rw [h2, mul_one]
  rw [key]
  calc _ ≤ (g : ℝ) ^ j * Lp g e ℓ * (g : ℝ) ^ (r - e) := hcast
    _ ≤ s ^ (2 * e) * s ^ e * (g : ℝ) ^ (r - e) := by gcongr
    _ = (g : ℝ) ^ (r - e) * s ^ (3 * e) := by ring
end PI.SqfRootsInj.W
