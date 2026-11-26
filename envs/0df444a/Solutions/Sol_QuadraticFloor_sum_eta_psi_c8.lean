-- Prove2me | solution 1 for QuadraticFloor.sum_eta_psi_c8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:01.342797+00:00
-- url     : https://prove2.me/submissions/45bb98ce-0690-4f2f-8d1b-8eaf0e822db1

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
public import Theorems.Thm_QuadraticFloor_cast_add_of_dvd
public import Theorems.Thm_QuadraticFloor_cast8_add_half
public import Theorems.Thm_QuadraticFloor_not_dvd_eight_mul
public import Theorems.Thm_P2M_QuadraticFloor_eta_eq__74b5fa8b45c2
public import Theorems.Thm_P2M_QuadraticFloor_half_sum_zero_of_periodic__7707a5ec64ba
public import Theorems.Thm_QuadraticFloor_eta_add_half
public import Theorems.Thm_QuadraticFloor_odd_of_ne_two
public import Theorems.Thm_QuadraticFloor_sum_mul_legendre_eq_zero


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {A : ℕ}
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (hA : Odd A) (hpA : ¬ p ∣ A) (ψ : DirichletCharacter ℂ A)
    (c : ZMod 8 → ℂ) (hc : ∀ y, c (y + 4) = -c y) :
    ∑ x ∈ Icc 1 (4 * A * p), (eta p x : ℂ) * ψ (x : ZMod A) * c (x : ZMod 8) = 0 := by
  have hAp : Odd (A * p) := hA.mul (odd_of_ne_two hp2)
  apply half_sum_zero_of_periodic' _ (h := 4 * A * p)
  · intro x
    rw [eta_add_half hp2 hA, cast8_add_half hAp,
      cast_add_of_dvd x _ A ⟨4 * p, by ring⟩, hc]
    push_cast; ring
  · rw [show 2 * (4 * A * p) = 8 * A * p by ring]
    have := sum_mul_legendre_eq_zero hp2
      (fun x => (kap p (x : ZMod 8) : ℂ) * ψ (x : ZMod A) * c (x : ZMod 8))
      (m := 8 * A) (not_dvd_eight_mul hp2 hpA) (by
        intro x
        rw [cast_add_of_dvd x _ 8 ⟨A, rfl⟩, cast_add_of_dvd x _ A ⟨8, by ring⟩])
    rw [← this]
    apply sum_congr rfl
    intro x _
    rw [eta_eq' hp2]
    push_cast; ring
end QuadraticFloor
