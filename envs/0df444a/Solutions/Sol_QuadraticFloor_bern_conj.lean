-- Prove2me | solution 1 for QuadraticFloor.bern_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:28.206032+00:00
-- url     : https://prove2.me/submissions/41ea1108-11de-4d81-bae0-7dc9372a484b

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (q : ℕ) (f : ℕ → ℂ) :
    bern q (fun x => starRingEnd ℂ (f x)) = starRingEnd ℂ (bern q f) := by
  unfold bern
  rw [map_mul, map_sum]
  congr 1
  · simp
  · apply sum_congr rfl; intro x _; rw [map_mul, Complex.conj_natCast]
end QuadraticFloor
