-- Prove2me | solution 1 for QuadraticFloor.kap_disc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:22.599226+00:00
-- url     : https://prove2.me/submissions/8c29acb2-cde7-46d7-a823-4ad47b19f1a4

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
public import Theorems.Thm_QuadraticFloor_kap_five
public import Theorems.Thm_QuadraticFloor_kap_one


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp
namespace QuadraticFloor
theorem _root_.solution {d : ℕ} {C : ℤ} (hd : d % 8 = if Even C then 1 else 5) :
    kap p (d : ZMod 8) = (C.negOnePow : ℤ) := by
  by_cases hC : Even C
  · simp only [hC, ite_true] at hd
    rw [Int.negOnePow_even C hC, show (d : ZMod 8) = 1 by
      rw [show (1 : ZMod 8) = ((1 : ℕ) : ZMod 8) by norm_num, ZMod.natCast_eq_natCast_iff']; omega,
      kap_one]
    rfl
  · simp only [hC, ite_false] at hd
    rw [Int.negOnePow_odd C (Int.not_even_iff_odd.1 hC), show (d : ZMod 8) = 5 by
      rw [show (5 : ZMod 8) = ((5 : ℕ) : ZMod 8) by norm_num, ZMod.natCast_eq_natCast_iff']; omega,
      kap_five]
    rfl
end QuadraticFloor
