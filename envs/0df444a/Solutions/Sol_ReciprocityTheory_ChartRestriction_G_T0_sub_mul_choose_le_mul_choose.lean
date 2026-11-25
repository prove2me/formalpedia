-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.sub_mul_choose_le_mul_choose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:31:06.669277+00:00
-- url     : https://prove2.me/submissions/a19fe9cf-f9a4-4d31-9b24-c6797f674160

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BinomRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.T0
private theorem choose_succ_mul_succ_eq_choose_mul_sub (n k : ℕ) (h : k ≤ n) :
    ((n.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((n.choose k : ℕ) : ℝ) * ((n : ℝ) - k) := by
  have h1 := Nat.choose_succ_right_eq n k
  have h2 : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := Nat.cast_sub h
  rw [← h2]
  exact_mod_cast h1
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (T D : ℕ) (hT : D * (2 * D + 7) ≤ T) :
    ∀ k ≤ D, ((T : ℝ) - k * (2 * D + 7)) * (((T + 2 * D + 6).choose k : ℕ) : ℝ) ≤
      (T : ℝ) * (((T - 1).choose k : ℕ) : ℝ) := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih (by omega)
    have h7 : 7 * D ≤ T := by nlinarith [Nat.zero_le (D * D)]
    have hA := choose_succ_mul_succ_eq_choose_mul_sub (T + 2 * D + 6) k (by omega)
    have hB := choose_succ_mul_succ_eq_choose_mul_sub (T - 1) k (by omega)
    have ha : ((T + 2 * D + 6 : ℕ) : ℝ) = (T : ℝ) + 2 * D + 6 := by push_cast; ring
    have hT1 : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [ha] at hA
    rw [hT1] at hB
    have hkT : ((k : ℝ) + 2) ≤ T := by exact_mod_cast (show k + 2 ≤ T by omega)
    have hb : (0 : ℝ) ≤ (T : ℝ) - 1 - k := by linarith
    have hCA : (0 : ℝ) ≤ (((T + 2 * D + 6).choose k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hdiff : (0 : ℝ) ≤ ((T : ℝ) - k * (2 * D + 7)) * ((T : ℝ) - 1 - k) -
        ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * ((T : ℝ) + 2 * D + 6 - k) := by
      have e : ((T : ℝ) - k * (2 * D + 7)) * ((T : ℝ) - 1 - k) -
          ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * ((T : ℝ) + 2 * D + 6 - k) =
          (2 * (D : ℝ) + 7) * ((k : ℝ) + 1) * (2 * (D : ℝ) + 6) := by ring
      rw [e]; positivity
    have P := mul_le_mul_of_nonneg_right ih hb
    have Q := mul_nonneg hCA hdiff
    have key : ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) *
        (((T + 2 * D + 6).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) ≤
        (T : ℝ) * (((T - 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) := by
      have e1 : ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) *
          (((T + 2 * D + 6).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) =
          ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) *
          ((((T + 2 * D + 6).choose k : ℕ) : ℝ) * ((T : ℝ) + 2 * D + 6 - k)) := by
        linear_combination ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * hA
      have e2 : (T : ℝ) * (((T - 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) =
          (T : ℝ) * ((((T - 1).choose k : ℕ) : ℝ) * ((T : ℝ) - 1 - k)) := by
        linear_combination (T : ℝ) * hB
      rw [e1, e2]
      nlinarith [P, Q]
    push_cast
    exact le_of_mul_le_mul_right key hk1
end ReciprocityTheory.ChartRestriction.G.T0
