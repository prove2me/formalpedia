-- Prove2me | solution 1 for QuadraticFloor.floorSum_eq_of_sq_modEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:06:04.483404+00:00
-- url     : https://prove2.me/submissions/3eef450f-2a4d-4acb-9e6f-a5ee74c4181c

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_floorSum_eq_of_sq_modEq__0734c730f8f6


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (hpA : ¬ p ∣ A)
    {B C B' C' : ℤ} (h : Admissible A B C) (h' : Admissible A B' C')
    (hBB : B ^ 2 ≡ B' ^ 2 [ZMOD A]) :
    floorSum A B C p = floorSum A B' C' p ∧ C.negOnePow = C'.negOnePow :=
  floorSum_eq_of_sq_modEq' hp2 hA hpA h h' hBB
end QuadraticFloor
