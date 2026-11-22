-- Prove2me | solution 1 for Pseudorandom.condAbsInc_adapted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:48:03.375261+00:00
-- url     : https://prove2.me/submissions/8c9faf7c-0c33-4657-a271-d9d7898dbaa0

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
namespace Pseudorandom
theorem _root_.solution (hX : ∀ k, Adapted k (X k)) (i : Fin n) :
    Adapted i (condAbsInc P X i) := by
  intro ω ω' hω
  unfold condAbsInc
  refine sum_congr rfl fun a _ => ?_
  congr 3
  · apply hX
    intro j hj
    by_cases hji : j = i
    · subst hji; simp
    · rw [Function.update_of_ne hji, Function.update_of_ne hji]
      exact hω j (by have : (j : ℕ) ≠ i := fun h => hji (Fin.ext h); omega)
  · exact hX i ω ω' hω
end Pseudorandom
