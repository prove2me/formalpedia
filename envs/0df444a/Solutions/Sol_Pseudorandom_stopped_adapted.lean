-- Prove2me | solution 1 for Pseudorandom.stopped_adapted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:36.384911+00:00
-- url     : https://prove2.me/submissions/3ed9f539-22c3-40af-8956-9c772a527489

module
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_Vendor_Freedman
public import Theorems.Thm_Pseudorandom_alive_adapted

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α] {n : ℕ}
variable {P : Fin n → α → ℝ} {X : ℕ → (Fin n → α) → ℝ} {G : ℕ → (Fin n → α) → Prop}
omit [Fintype α]
namespace Pseudorandom
theorem _root_.solution (hX : ∀ k, Adapted k (X k)) (hG : ∀ k, Adapted k (G k)) :
    ∀ k, Adapted k (stopped X G k)
  | 0 => hX 0
  | k + 1 => by
    intro ω ω' hω
    have ha := alive_adapted hG k ω ω' (fun i hi => hω i (by omega))
    simp only [stopped]
    simp only at ha
    rw [ha, hX (k + 1) ω ω' hω, solution hX hG k ω ω' (fun i hi => hω i (by omega))]
end Pseudorandom
