-- Prove2me | solution 1 for QuadraticFloor.char3_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:17.35077+00:00
-- url     : https://prove2.me/submissions/d2921aa7-041a-49fe-9388-987eaeef1081

module
public import Definitions.Def_QuadraticFloor_SquareClass
public import Definitions.Def_QuadraticFloor_Corollaries
public import Theorems.Thm_QuadraticFloor_chi3_two
public import Theorems.Thm_QuadraticFloor_zmod3_cases

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (ψ : DirichletCharacter ℂ 3) : ψ = 1 ∨ ψ = chi3 := by
  have h4 : ψ 2 ^ 2 = 1 := by rw [← map_pow, show (2 : ZMod 3) ^ 2 = 1 by decide, map_one]
  have hu : ∀ a : ZMod 3, a ≠ 0 → IsUnit a := by
    intro a ha; rcases zmod3_cases a with h | h | h
    · exact absurd h ha
    · rw [h]; exact isUnit_one
    · rw [h]; exact IsUnit.of_mul_eq_one (2 : ZMod 3) (by decide)
  rcases (mul_self_eq_one_iff (a := ψ 2)).1 (by rw [← pow_two]; exact h4) with h | h
  · left
    refine MulChar.ext' fun a => ?_
    rcases zmod3_cases a with ha | ha | ha
    · rw [ha, MulChar.map_nonunit _ (by decide), MulChar.map_nonunit _ (by decide)]
    · rw [ha, map_one, map_one]
    · rw [ha, h, MulChar.one_apply (hu 2 (by decide))]
  · right
    refine MulChar.ext' fun a => ?_
    rcases zmod3_cases a with ha | ha | ha
    · rw [ha, MulChar.map_nonunit _ (by decide), MulChar.map_nonunit _ (by decide)]
    · rw [ha, map_one, map_one]
    · rw [ha, h, chi3_two]
end QuadraticFloor
