-- Prove2me | solution 1 for PI.SqfRootsInj.W.termB_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:31:44.459262+00:00
-- url     : https://prove2.me/submissions/71710e89-0b60-4474-9805-61a4edd72787

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
theorem _root_.solution (g r e e' ℓ : ℕ) (s : ℝ) (hs0 : 0 < s) (hs4 : s ^ 4 = g)
    (hℓ : ℓ.Prime) (hB : ℓ ∉ BB r g) (he1 : 1 ≤ e) (hsum : e + e' ≤ r) :
    ((g ^ e' * Lp g e ℓ * g ^ (r - e - e') : ℕ) : ℝ) ≤ (g : ℝ) ^ r * (s⁻¹) ^ (3 * e) := by
  have hL : (Lp g e ℓ : ℝ) ≤ s ^ e := by
    have h4 : ((Lp g e ℓ : ℝ)) ^ 4 ≤ (s ^ e) ^ 4 := by
      rw [← pow_mul, mul_comm e 4, pow_mul, hs4]
      exact_mod_cast lp_pow_four_le hℓ hB he1 (by omega)
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h4
  have key : (g : ℝ) ^ r * (s⁻¹) ^ (3 * e) = (g : ℝ) ^ e' * s ^ e * (g : ℝ) ^ (r - e - e') := by
    have h1 : (g : ℝ) ^ r = (g : ℝ) ^ (r - e - e') * (g : ℝ) ^ e' * (s ^ 4) ^ e := by
      rw [hs4, ← pow_add, ← pow_add]; congr 1; omega
    have h2 : s ^ (3 * e) * (s⁻¹) ^ (3 * e) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hs0.ne', one_pow]
    rw [h1]
    calc (g : ℝ) ^ (r - e - e') * (g : ℝ) ^ e' * (s ^ 4) ^ e * (s⁻¹) ^ (3 * e)
        = (g : ℝ) ^ e' * s ^ e * (g : ℝ) ^ (r - e - e') * (s ^ (3 * e) * (s⁻¹) ^ (3 * e)) := by
          ring
      _ = _ := by rw [h2, mul_one]
  rw [key]
  push_cast
  gcongr
end PI.SqfRootsInj.W
