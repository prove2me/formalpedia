-- Prove2me | solution 1 for QuadraticFloor.char5_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:43.666291+00:00
-- url     : https://prove2.me/submissions/e248d14e-11ad-40e1-b282-6e6e52868808

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (ψ : DirichletCharacter ℂ 5) :
    ψ 2 = 1 ∨ ψ 2 = Complex.I ∨ ψ 2 = -1 ∨ ψ 2 = -Complex.I := by
  have h4 : ψ 2 ^ 4 = 1 := by rw [← map_pow, show (2 : ZMod 5) ^ 4 = 1 by decide, map_one]
  have hf : (ψ 2 - 1) * (ψ 2 + 1) * ((ψ 2 - Complex.I) * (ψ 2 + Complex.I)) = 0 := by
    have : (ψ 2 - Complex.I) * (ψ 2 + Complex.I) = ψ 2 ^ 2 + 1 := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [this]; linear_combination h4
  rcases mul_eq_zero.1 hf with h | h
  · rcases mul_eq_zero.1 h with h | h
    · left; linear_combination h
    · right; right; left; linear_combination h
  · rcases mul_eq_zero.1 h with h | h
    · right; left; linear_combination h
    · right; right; right; linear_combination h
end QuadraticFloor
