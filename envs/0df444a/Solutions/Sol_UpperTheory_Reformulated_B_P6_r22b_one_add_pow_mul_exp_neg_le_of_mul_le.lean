-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.r22b.one_add_pow_mul_exp_neg_le_of_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:46:52.195519+00:00
-- url     : https://prove2.me/submissions/94a0e10a-ce31-4f13-bb3f-f2075c05ca56

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_OneAddPowMulExpLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r22b
namespace UpperTheory.Reformulated.B.P6.r22b
theorem _root_.solution (K : ℕ) {a β s : ℝ} (ha : 0 < a) (hKa : (K : ℝ) * a ≤ β) (hs : 0 ≤ s) :
    (1 + s) ^ K * Real.exp (-β * s) ≤ (1 + 1 / a) ^ K := by
  have e : 1 / a * (a * s) = s := by
    rw [← mul_assoc, one_div_mul_cancel ha.ne', one_mul]
  have has : 0 ≤ a * s := mul_nonneg ha.le hs
  have hia : 0 < 1 / a := one_div_pos.mpr ha
  have h1 : 1 + s ≤ (1 + 1 / a) * (1 + a * s) := by
    calc 1 + s ≤ 1 + a * s + 1 / a + 1 / a * (a * s) := by rw [e]; linarith
      _ = (1 + 1 / a) * (1 + a * s) := by ring
  have h2 : 1 + a * s ≤ Real.exp (a * s) := by
    linarith [Real.add_one_le_exp (a * s)]
  have h3 : (1 + s) ^ K ≤ (1 + 1 / a) ^ K * Real.exp (a * s) ^ K := by
    rw [← mul_pow]
    have h4 : 1 + s ≤ (1 + 1 / a) * Real.exp (a * s) :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 (by linarith))
    exact pow_le_pow_left₀ (by linarith) h4 K
  have h5 : Real.exp (a * s) ^ K * Real.exp (-β * s) ≤ 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    rw [Real.exp_le_one_iff]
    have : (K : ℝ) * (a * s) = ((K : ℝ) * a) * s := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_right hKa hs]
  have hc : 0 ≤ (1 + 1 / a) ^ K := pow_nonneg (by linarith) K
  have hE : 0 ≤ Real.exp (-β * s) := (Real.exp_pos _).le
  calc (1 + s) ^ K * Real.exp (-β * s)
      ≤ (1 + 1 / a) ^ K * Real.exp (a * s) ^ K * Real.exp (-β * s) :=
        mul_le_mul_of_nonneg_right h3 hE
    _ = (1 + 1 / a) ^ K * (Real.exp (a * s) ^ K * Real.exp (-β * s)) := by ring
    _ ≤ (1 + 1 / a) ^ K * 1 := mul_le_mul_of_nonneg_left h5 hc
    _ = (1 + 1 / a) ^ K := mul_one _
end UpperTheory.Reformulated.B.P6.r22b
