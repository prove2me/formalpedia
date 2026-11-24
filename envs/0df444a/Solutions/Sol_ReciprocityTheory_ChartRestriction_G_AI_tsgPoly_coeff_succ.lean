-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.tsgPoly_coeff_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:07.331502+00:00
-- url     : https://prove2.me/submissions/ef1ec53d-1905-4952-849c-da6ae1202749

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_APrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Polynomial
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (D : ℕ) (κ : ℕ → ℝ) (P : ℝ[X]) (m : ℕ) :
    (tsgPoly D κ P).coeff (m + 1) =
      if Odd m then ((D : ℝ) + 1) * κ ((m + 1) / 2) / (((m + 1) / 2 : ℕ) : ℝ) * P.coeff m else 0 := by
  rw [tsgPoly, Polynomial.finset_sum_coeff, Finset.sum_eq_single m]
  · by_cases ho : Odd m
    · rw [if_pos ho, if_pos ho, Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · rw [if_neg ho, if_neg ho, Polynomial.coeff_zero]
  · intro n _ hnm
    by_cases ho : Odd n
    · rw [if_pos ho, Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
    · rw [if_neg ho, Polynomial.coeff_zero]
  · intro hm
    have h0 : P.coeff m = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at hm; omega)
    by_cases ho : Odd m
    · rw [if_pos ho, Polynomial.coeff_C_mul_X_pow, if_pos rfl, h0, mul_zero]
    · rw [if_neg ho, Polynomial.coeff_zero]
end ReciprocityTheory.ChartRestriction.G.AI
