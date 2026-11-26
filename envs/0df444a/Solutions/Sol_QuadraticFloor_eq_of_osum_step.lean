-- Prove2me | solution 1 for QuadraticFloor.eq_of_osum_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:21.034377+00:00
-- url     : https://prove2.me/submissions/2d015392-1632-4eab-a404-48eeac433ee4

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
public import Theorems.Thm_QuadraticFloor_osum_zero
public import Theorems.Thm_QuadraticFloor_osum_succ

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution {F : ℤ → ℤ} {g : ℤ → ℤ} (hF : ∀ c, F (c + 1) = F c + g c) (c : ℤ) :
    F c = F 0 + osum c g := by
  induction c using Int.induction_on with
  | zero => rw [osum_zero, add_zero]
  | succ i ih => rw [hF, ih, osum_succ]; ring
  | pred i ih =>
    have h1 := hF (-(i : ℤ) - 1)
    have h2 := osum_succ (-(i : ℤ) - 1) g
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at h1 h2
    rw [ih] at h1
    linarith
end QuadraticFloor
