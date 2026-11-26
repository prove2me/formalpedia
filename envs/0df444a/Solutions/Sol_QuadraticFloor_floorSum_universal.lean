-- Prove2me | solution 1 for QuadraticFloor.floorSum_universal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:06:01.407722+00:00
-- url     : https://prove2.me/submissions/abd5d9d6-0f0b-480e-bacd-45d7ffb8aa12

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_floorSum_universal__ec9587aa8f07


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) {A : ℕ} [NeZero A] (hA : Odd A) (hpA : ¬ p ∣ A) :
    (floorSum A 1 0 p : ℂ) = 1 - (1 / (A.totient : ℂ)) *
      ∑ ψ : DirichletCharacter ℂ A, bern (8 * A * p) (vartheta p ψ) :=
  floorSum_universal' hp2 hA hpA
end QuadraticFloor
