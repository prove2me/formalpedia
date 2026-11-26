-- Prove2me | solution 1 for QuadraticFloor.eta_add_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:55:49.225828+00:00
-- url     : https://prove2.me/submissions/d252a89b-7db9-4e59-92fa-b150ae29d3ff

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta
public import Theorems.Thm_QuadraticFloor_kap_add_four
public import Theorems.Thm_P2M_QuadraticFloor_eta_eq__74b5fa8b45c2
public import Theorems.Thm_QuadraticFloor_odd_of_ne_two


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (x : ℕ) :
    eta p (x + 4 * A * p) = -eta p x := by
  rw [eta_eq' hp2, eta_eq' hp2]
  have hAp : (A * p) % 2 = 1 := Nat.odd_iff.1 (hA.mul (odd_of_ne_two hp2))
  have hm : (4 * A * p) % 8 = 4 % 8 := by rw [show 4 * A * p = 4 * (A * p) by ring]; omega
  have h4 : ((4 * A * p : ℕ) : ZMod 8) = 4 := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ 8).2 hm
    rw [Nat.cast_ofNat] at this
    exact this
  have h8 : ((x + 4 * A * p : ℕ) : ZMod 8) = (x : ZMod 8) + 4 := by
    rw [Nat.cast_add, h4]
  have hL : legendreSym p ((x + 4 * A * p : ℕ) : ℤ) = legendreSym p x := by
    rw [legendreSym.mod, legendreSym.mod p (x : ℤ)]
    congr 1
    push_cast
    rw [show (x : ℤ) + 4 * A * p = x + (4 * A) * p by ring, Int.add_mul_emod_self_right]
  rw [h8, hL, kap_add_four]
  ring
end QuadraticFloor
