-- Prove2me | solution 1 for Pseudorandom.stopped_eq_of_alive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:33.633481+00:00
-- url     : https://prove2.me/submissions/0c413d04-4d08-45f2-a94b-2e3d5341240c

module
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_Vendor_Freedman

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α] {n : ℕ}
variable {P : Fin n → α → ℝ} {X : ℕ → (Fin n → α) → ℝ} {G : ℕ → (Fin n → α) → Prop}
omit [Fintype α]
namespace Pseudorandom
theorem _root_.solution {ω : Fin n → α} :
    ∀ k, (k = 0 ∨ Alive G (k - 1) ω) → stopped X G k ω = X k ω
  | 0, _ => rfl
  | k + 1, h => by
    have hk : Alive G k ω := by
      rcases h with h | h
      · omega
      · simpa using h
    simp [stopped, hk]
end Pseudorandom
