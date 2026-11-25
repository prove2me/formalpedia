-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.volPoly_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:50.77741+00:00
-- url     : https://prove2.me/submissions/2ccd4c10-264e-4621-86c5-16a389346fa2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_APrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.AI
open Polynomial
private theorem neg_X_pow_eq_C_neg_one_pow_mul_X_pow (j : ℕ) : ((-X : ℝ[X]) ^ j) = C ((-1 : ℝ) ^ j) * X ^ j := by
  have hX : (-X : ℝ[X]) = C (-1) * X := by
    ext n
    rw [Polynomial.coeff_neg, Polynomial.coeff_C_mul]
    ring
  rw [hX, mul_pow, ← map_pow]
end ReciprocityTheory.ChartRestriction.G.AI
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Polynomial
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (D : ℕ) (J : ℕ → ℝ) (n : ℕ) :
    (volPoly D J).coeff n = (D.choose n : ℝ) * J n * (-1) ^ n := by
  have h : ∀ j, (C ((D.choose j : ℝ) * J j) * (-X) ^ j : ℝ[X]) =
      C ((D.choose j : ℝ) * J j * (-1) ^ j) * X ^ j := by
    intro j
    rw [neg_X_pow_eq_C_neg_one_pow_mul_X_pow, ← mul_assoc, ← map_mul]
  rw [volPoly, Finset.sum_congr rfl fun j _ => h j, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hn
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by simp at hn; omega)]
    simp
end ReciprocityTheory.ChartRestriction.G.AI
