-- Prove2me | solution 1 for Pseudorandom.alive_adapted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:36:21.45001+00:00
-- url     : https://prove2.me/submissions/58ff3220-bc7b-47b1-a84f-d94537a2918e

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
theorem _root_.solution (hG : ∀ k, Adapted k (G k)) (k : ℕ) :
    Adapted k (fun ω => Alive G k ω) := by
  intro ω ω' hω
  apply propext
  unfold Alive
  constructor
  · intro h j hj
    have := hG j ω ω' (fun i hi => hω i (by omega))
    rw [← this]; exact h j hj
  · intro h j hj
    have := hG j ω ω' (fun i hi => hω i (by omega))
    rw [this]; exact h j hj
end Pseudorandom
