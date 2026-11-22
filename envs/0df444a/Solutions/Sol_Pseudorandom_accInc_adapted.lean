-- Prove2me | solution 1 for Pseudorandom.accInc_adapted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:44.461809+00:00
-- url     : https://prove2.me/submissions/25ce0cbe-5fe4-4cab-b43a-aec135b55356

module
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_Vendor_Freedman
public import Theorems.Thm_Pseudorandom_alive_adapted
public import Theorems.Thm_Pseudorandom_condAbsInc_adapted

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α] {n : ℕ}
variable {P : Fin n → α → ℝ} {X : ℕ → (Fin n → α) → ℝ} {G : ℕ → (Fin n → α) → Prop}
namespace Pseudorandom
theorem _root_.solution (hX : ∀ k, Adapted k (X k)) (hG : ∀ k, Adapted k (G k)) :
    ∀ k, Adapted k (accInc P X G k)
  | 0 => fun _ _ _ => rfl
  | k + 1 => by
    intro ω ω' hω
    have ha := alive_adapted hG k ω ω' (fun i hi => hω i (by omega))
    have hA := solution hX hG k ω ω' (fun i hi => hω i (by omega))
    simp only at ha
    simp only [accInc]
    split_ifs with h1 h2 h3 h3
    · rw [hA, condAbsInc_adapted hX ⟨k, h1⟩ ω ω' (fun i hi => hω i (by simp at hi; omega))]
    · exact absurd (ha ▸ h2) h3
    · exact absurd (ha ▸ h3) h2
    · exact hA
    · exact hA
end Pseudorandom
