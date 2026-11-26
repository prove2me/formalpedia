-- Prove2me | solution 1 for P2M_QuadraticFloor_floorSum_universal__ec9587aa8f07
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:01:51.500159+00:00
-- url     : https://prove2.me/submissions/aaf19f47-8649-4bfc-9aeb-44c054eb9747

module
public import Definitions.Def_QuadraticFloor_SquareClass
public import Definitions.Def_QuadraticFloor_Corollaries
public import Theorems.Thm_P2M_QuadraticFloor_square_class_decomposition__92217ce4d4b4


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) {A : ℕ} [NeZero A] (hA : Odd A) (hpA : ¬ p ∣ A) :
    (floorSum A 1 0 p : ℂ) = 1 - (1 / (A.totient : ℂ)) *
      ∑ ψ : DirichletCharacter ℂ A, bern (8 * A * p) (vartheta p ψ) := by
  have hadm : Admissible A 1 0 := ⟨odd_one, by simp, by simp, by
    have := hA.pos; push_cast; omega⟩
  rw [square_class_decomposition' hp2 hA hpA hadm]
  simp
end QuadraticFloor
