-- Prove2me | solution 1 for QuadraticFloor.sum_eta_psi_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:06.199354+00:00
-- url     : https://prove2.me/submissions/8f2f5914-a16f-4d37-85df-80d3726327c7

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
public import Theorems.Thm_QuadraticFloor_cast_add_of_dvd
public import Theorems.Thm_QuadraticFloor_psi_reflect
public import Theorems.Thm_P2M_QuadraticFloor_half_sum_zero_of_even__ebacac1c3808
public import Theorems.Thm_QuadraticFloor_eta_add_half
public import Theorems.Thm_QuadraticFloor_eta_of_even
public import Theorems.Thm_QuadraticFloor_eta_reflect


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {A : ℕ}
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (hA : Odd A) (ψ : DirichletCharacter ℂ A) (c : ℕ → ℂ)
    (s : ℂ) (hcper : ∀ x, c (x + 4 * A * p) = c x)
    (hcref : ∀ x ≤ 8 * A * p, c (8 * A * p - x) = s * c x) (hs : s * ψ (-1) = -1) :
    ∑ x ∈ Icc 1 (4 * A * p), (eta p x : ℂ) * ψ (x : ZMod A) * c x = 0 := by
  apply half_sum_zero_of_even' _ (h := 4 * A * p)
  · intro x
    rw [eta_add_half hp2 hA, cast_add_of_dvd x _ A ⟨4 * p, by ring⟩, hcper]
    push_cast; ring
  · rw [eta_of_even (⟨0, rfl⟩ : Even 0)]; simp
  · intro x hx
    rw [show 2 * (4 * A * p) = 8 * A * p by ring] at hx ⊢
    rw [eta_reflect hp2 ⟨A, by ring⟩ hx, psi_reflect ψ hx ⟨8 * p, by ring⟩, hcref x hx]
    push_cast
    linear_combination (-(eta p x : ℂ) * ψ (x : ZMod A) * c x) * hs
end QuadraticFloor
