-- Prove2me | solution 1 for UnramifiedWhittaker.norm_heckeRecursionSeq_le_mul_pow_of_norm_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/320ed5ae-ca92-569e-add8-39b5be7d8e1e

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UnramifiedWhittaker_norm_heckeRecursionSeq_le_mul_pow_of_norm_le_rpow

set_option autoImplicit false

open UnramifiedWhittaker

theorem solution
    (q κ : ℝ) (hq : 1 ≤ q) (hκ : 0 ≤ κ) (lam om : ℂ)
    (hlam : ‖lam‖ ≤ q ^ κ) (hom : ‖om‖ ≤ q ^ κ) (m : ℕ) :
    ‖heckeRecursionSeq (q : ℂ) lam om m‖ ≤ ((m : ℝ) + 1) * (2 * q ^ κ) ^ m := by
  have hq0 : 0 < q := by linarith
  have hqn : ‖(q : ℂ)‖ = q := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
  have hc1 : 1 ≤ q ^ κ := Real.one_le_rpow hq hκ
  have hc0 : 0 ≤ q ^ κ := by linarith
  set A : ℝ := 2 * q ^ κ with hA
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hA2 : 2 ≤ A := by rw [hA]; linarith

  have key : ∀ n : ℕ, ‖heckeRecursionSeq (q : ℂ) lam om n‖ ≤ ((n : ℝ) + 1) * A ^ n ∧
      ‖heckeRecursionSeq (q : ℂ) lam om (n + 1)‖ ≤ ((n : ℝ) + 2) * A ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [heckeRecursionSeq]
      · show ‖lam / (q : ℂ)‖ ≤ (((0 : ℕ) : ℝ) + 2) * A ^ (0 + 1)
        rw [norm_div, hqn, div_le_iff₀ hq0]
        calc ‖lam‖ ≤ q ^ κ := hlam
          _ ≤ (((0 : ℕ) : ℝ) + 2) * A ^ (0 + 1) * q := by
              rw [hA]; push_cast
              nlinarith
    | succ n ih =>
      obtain ⟨h0, h1⟩ := ih
      refine ⟨by
        have e : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
        rw [e]; exact h1, ?_⟩
      show ‖(lam * heckeRecursionSeq (q : ℂ) lam om (n + 1) - om * heckeRecursionSeq (q : ℂ) lam om n) / (q : ℂ)‖ ≤
        (((n + 1 : ℕ) : ℝ) + 2) * A ^ (n + 1 + 1)
      rw [norm_div, hqn, div_le_iff₀ hq0]
      have hu0 : 0 ≤ ‖heckeRecursionSeq (q : ℂ) lam om n‖ := norm_nonneg _
      have hu1 : 0 ≤ ‖heckeRecursionSeq (q : ℂ) lam om (n + 1)‖ := norm_nonneg _
      have hAn : 0 ≤ A ^ n := pow_nonneg hA0 n
      calc ‖lam * heckeRecursionSeq (q : ℂ) lam om (n + 1) - om * heckeRecursionSeq (q : ℂ) lam om n‖
          ≤ ‖lam‖ * ‖heckeRecursionSeq (q : ℂ) lam om (n + 1)‖ + ‖om‖ * ‖heckeRecursionSeq (q : ℂ) lam om n‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ q ^ κ * (((n : ℝ) + 2) * A ^ (n + 1)) + q ^ κ * (((n : ℝ) + 1) * A ^ n) := by
            gcongr
        _ = q ^ κ * A ^ n * (((n : ℝ) + 2) * A + ((n : ℝ) + 1)) := by ring
        _ ≤ q ^ κ * A ^ n * (((n : ℝ) + 2) * A + ((n : ℝ) + 1) * A) := by
            have hn1 : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) * A :=
              le_mul_of_one_le_right (by positivity) (by linarith)
            have hpos : 0 ≤ q ^ κ * A ^ n := mul_nonneg hc0 hAn
            nlinarith
        _ = (2 * (n : ℝ) + 3) * (q ^ κ * A ^ (n + 1)) := by ring
        _ ≤ (((n + 1 : ℕ) : ℝ) + 2) * A ^ (n + 1 + 1) * q := by
            push_cast
            have hApow : 0 ≤ q ^ κ * A ^ (n + 1) := mul_nonneg hc0 (pow_nonneg hA0 _)

            have e : ((n : ℝ) + 1 + 2) * A ^ (n + 1 + 1) * q = (2 * (n : ℝ) + 6) * (q ^ κ * A ^ (n + 1)) * q := by
              rw [hA]; ring
            rw [e]
            have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            calc (2 * (n : ℝ) + 3) * (q ^ κ * A ^ (n + 1)) ≤ (2 * (n : ℝ) + 6) * (q ^ κ * A ^ (n + 1)) :=
                  mul_le_mul_of_nonneg_right (by linarith) hApow
              _ = (2 * (n : ℝ) + 6) * (q ^ κ * A ^ (n + 1)) * 1 := by ring
              _ ≤ (2 * (n : ℝ) + 6) * (q ^ κ * A ^ (n + 1)) * q :=
                  mul_le_mul_of_nonneg_left hq (mul_nonneg (by linarith) hApow)
  exact (key m).1

#print axioms solution

end S_UnramifiedWhittaker_norm_heckeRecursionSeq_le_mul_pow_of_norm_le_rpow
end P2MW
export P2MW.S_UnramifiedWhittaker_norm_heckeRecursionSeq_le_mul_pow_of_norm_le_rpow (solution)
