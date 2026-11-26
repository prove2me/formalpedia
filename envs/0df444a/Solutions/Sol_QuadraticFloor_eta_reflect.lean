-- Prove2me | solution 1 for QuadraticFloor.eta_reflect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:55:31.648898+00:00
-- url     : https://prove2.me/submissions/ad8db743-9573-4969-a605-210a9155dcec

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta
public import Theorems.Thm_QuadraticFloor_kap_neg
public import Theorems.Thm_QuadraticFloor_kap_neg_one_mul_legendre
public import Theorems.Thm_P2M_QuadraticFloor_eta_eq__74b5fa8b45c2

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) {q : ℕ} (hq : 8 * p ∣ q) {x : ℕ} (hx : x ≤ q) :
    eta p (q - x) = -eta p x := by
  rw [eta_eq' hp2, eta_eq' hp2]
  have h8 : ((q - x : ℕ) : ZMod 8) = -(x : ZMod 8) := by
    rw [Nat.cast_sub hx, (ZMod.natCast_eq_zero_iff q 8).2 (dvd_trans (dvd_mul_right 8 p) hq),
      zero_sub]
  have hL : legendreSym p ((q - x : ℕ) : ℤ) = legendreSym p (-1) * legendreSym p x := by
    rw [← legendreSym.mul, legendreSym.mod, legendreSym.mod p (-1 * (x : ℤ))]
    congr 1
    rw [Nat.cast_sub hx]
    obtain ⟨r, hr⟩ := hq
    rw [hr]
    push_cast
    rw [show (8 * (p : ℤ) * r - x) = -1 * x + (8 * r) * p by ring, Int.add_mul_emod_self_right]
  rw [h8, hL, kap_neg]
  have := kap_neg_one_mul_legendre hp2
  linear_combination (kap p (x : ZMod 8) * legendreSym p x) * this
end QuadraticFloor
