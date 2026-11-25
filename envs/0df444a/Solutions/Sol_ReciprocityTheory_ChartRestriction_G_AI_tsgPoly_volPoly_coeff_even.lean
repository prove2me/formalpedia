-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.tsgPoly_volPoly_coeff_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:36:17.953223+00:00
-- url     : https://prove2.me/submissions/463cc66a-bb38-48aa-ad6d-78ed686e7ddd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_APrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_volPoly_coeff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_tsgPoly_coeff_succ

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
theorem _root_.solution (D : ℕ) (J κ : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (tsgPoly D κ (volPoly D J)).coeff (2 * k) =
      -(2 * ((D + 1).choose (2 * k) : ℝ) * (κ k * J (2 * k - 1))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h2 : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
  have h3 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
  have hodd : Odd (2 * j + 1) := ⟨j, rfl⟩
  rw [h2, tsgPoly_coeff_succ, if_pos hodd, volPoly_coeff, h3, Nat.add_sub_cancel,
    Odd.neg_one_pow hodd]
  have hc : (D + 1) * D.choose (2 * j + 1) = (D + 1).choose (2 * j + 1 + 1) * (2 * j + 1 + 1) := by
    first
    | exact Nat.add_one_mul_choose_eq D (2 * j + 1)
    | exact Nat.succ_mul_choose_eq D (2 * j + 1)
  have hc' : ((D : ℝ) + 1) * (D.choose (2 * j + 1) : ℝ) =
      ((D + 1).choose (2 * j + 1 + 1) : ℝ) * (2 * j + 1 + 1) := by exact_mod_cast hc
  have hj : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast at hj ⊢
  field_simp
  first
  | linear_combination (κ (j + 1) * J (2 * j + 1)) * hc'
  | linear_combination (-(κ (j + 1) * J (2 * j + 1))) * hc'
  | linear_combination (2 * κ (j + 1) * J (2 * j + 1)) * hc'
  | linear_combination (-(2 * κ (j + 1) * J (2 * j + 1))) * hc'
end ReciprocityTheory.ChartRestriction.G.AI
