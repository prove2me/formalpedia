-- Prove2me | solution 1 for RamanujanNagell.corollary_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:45:21.872592+00:00
-- url     : https://prove2.me/submissions/82fb4799-0607-49aa-a392-cbf9f2875173

module
public import Definitions.Def_LeanPool_RamanujanNagell_Helpers
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_RamanujanNagell_Basic

set_option autoImplicit true
@[expose] public section
public section
open RamanujanNagell
open Polynomial QuadraticAlgebra Algebra Nat
  UniqueFactorizationMonoid
namespace RamanujanNagell
theorem _root_.solution (x₁ x₂ : ℤ) (m₁ m₂ : ℕ)
    (h₁_odd : Odd m₁) (h₂_odd : Odd m₂)
    (h₁_ge : m₁ ≥ 3) (h₂_ge : m₂ ≥ 3)
    (h₁_eq : (x₁ ^ 2 + 7) / 4 = 2 ^ m₁)
    (h₂_eq : (x₂ ^ 2 + 7) / 4 = 2 ^ m₂) :
    θ ^ m₁ - θ' ^ m₁ = θ ^ m₂ - θ' ^ m₂ := by
  have h1 := main_m_condition x₁ m₁ h₁_odd h₁_ge h₁_eq
  have h2 := main_m_condition x₂ m₂ h₂_odd h₂_ge h₂_eq
  rw [← h1, ← h2]
end RamanujanNagell
