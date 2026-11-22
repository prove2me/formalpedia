-- Prove2me | solution 1 for Pseudorandom.IsExposureMartingale.neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:00:55.582814+00:00
-- url     : https://prove2.me/submissions/51c2c841-df54-4c3f-abe6-be4918684c46

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
namespace IsExposureMartingale
theorem _root_.solution (hX : IsExposureMartingale P X) :
    IsExposureMartingale P (fun k ω => -X k ω) := by
  refine ⟨fun k ω ω' h => by simp only [hX.1 k ω ω' h], fun i ω => ?_⟩
  simp only
  rw [hX.2 i ω, ← sum_neg_distrib]
  exact sum_congr rfl fun a _ => by ring
end IsExposureMartingale
end Pseudorandom
