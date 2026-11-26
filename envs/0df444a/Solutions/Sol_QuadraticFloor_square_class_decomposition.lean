-- Prove2me | solution 1 for QuadraticFloor.square_class_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:05:53.510383+00:00
-- url     : https://prove2.me/submissions/d8aa2def-bf3c-4800-8397-74fb73edf382

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_square_class_decomposition__92217ce4d4b4


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) {A : ℕ} [NeZero A] (hA : Odd A)
    (hpA : ¬ p ∣ A) {B C : ℤ} (hBC : Admissible A B C) :
    (floorSum A B C p : ℂ) = (C.negOnePow : ℤ) - (1 / (A.totient : ℂ)) *
      ∑ ψ : DirichletCharacter ℂ A, (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 *
        bern (8 * A * p) (vartheta p ψ) :=
  square_class_decomposition' hp2 hA hpA hBC
end QuadraticFloor
