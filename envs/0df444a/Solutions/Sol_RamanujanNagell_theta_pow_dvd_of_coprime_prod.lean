-- Prove2me | solution 1 for RamanujanNagell.theta_pow_dvd_of_coprime_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:42.931187+00:00
-- url     : https://prove2.me/submissions/2e9b6649-052c-459e-8e9c-6a17f63bd49e

module
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_RamanujanNagell_Helpers
public import Theorems.Thm_RamanujanNagell_theta_prime

set_option autoImplicit true
@[expose] public section
public section
open RamanujanNagell
open QuadraticAlgebra
namespace RamanujanNagell
theorem _root_.solution (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β) :
    θ ^ m ∣ α ∨ θ ^ m ∣ β := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Or.inl (one_dvd α)
  have hθ_prime : _root_.Prime θ := theta_prime
  have h_dvd_prod : θ ^ m ∣ α * β := h_prod ▸ dvd_mul_right (θ ^ m) (θ' ^ m)
  have h_dvd_or : θ ∣ α ∨ θ ∣ β :=
    hθ_prime.dvd_or_dvd (dvd_trans (dvd_pow_self θ (by omega)) h_dvd_prod)
  rcases h_dvd_or with h_dvd_α | h_dvd_β
  · have h_not_dvd_β : ¬ (θ ∣ β) := fun h_dvd_β =>
      hθ_prime.not_isUnit (h_coprime.isUnit_of_dvd' h_dvd_α h_dvd_β)
    exact Or.inl (hθ_prime.pow_dvd_of_dvd_mul_right m h_not_dvd_β h_dvd_prod)
  · have h_not_dvd_α : ¬ (θ ∣ α) := fun h_dvd_α =>
      hθ_prime.not_isUnit (h_coprime.isUnit_of_dvd' h_dvd_α h_dvd_β)
    exact Or.inr (hθ_prime.pow_dvd_of_dvd_mul_left m h_not_dvd_α h_dvd_prod)
end RamanujanNagell
