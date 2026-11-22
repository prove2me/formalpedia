-- Prove2me | solution 1 for Pseudorandom.accInc_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:25:27.538797+00:00
-- url     : https://prove2.me/submissions/d4ec24c2-0ce8-4c84-b6ca-d61103aad649

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
theorem _root_.solution (hP : IsPMF P) : ∀ k ω, 0 ≤ accInc P X G k ω
  | 0, _ => le_rfl
  | k + 1, ω => by
    have h0 := solution hP k ω
    simp only [accInc]
    split_ifs
    · have : 0 ≤ condAbsInc P X ⟨k, by omega⟩ ω :=
        sum_nonneg fun a _ => mul_nonneg (hP.1 _ a) (abs_nonneg _)
      linarith
    all_goals exact h0
end Pseudorandom
