-- Prove2me | solution 1 for Pseudorandom.IsExposureMartingale.pE_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:25:28.077043+00:00
-- url     : https://prove2.me/submissions/2cd1d646-37aa-42f7-b680-e0ac2c8f7eba

module
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_Vendor_Freedman
public import Theorems.Thm_Pseudorandom_pE_resample
public import Theorems.Thm_Pseudorandom_pE_const


set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α] {n : ℕ}
variable {P : Fin n → α → ℝ} {X : ℕ → (Fin n → α) → ℝ} {G : ℕ → (Fin n → α) → Prop}
namespace Pseudorandom
namespace IsExposureMartingale
theorem _root_.solution (hP : IsPMF P) (hX : IsExposureMartingale P X)
    (ω₀ : Fin n → α) : ∀ k, k ≤ n → pE P (X k) = X 0 ω₀
  | 0, _ => by
    have : X 0 = fun _ => X 0 ω₀ := funext fun ω =>
      hX.1 0 ω ω₀ fun i hi => absurd hi (by omega)
    rw [this, pE_const hP]
  | k + 1, hk => by
    rw [← solution hP hX ω₀ k (by omega), ← pE_resample hP ⟨k, by omega⟩ (X (k + 1))]
    congr 1
    funext ω
    exact (hX.2 ⟨k, by omega⟩ ω).symm
end IsExposureMartingale
end Pseudorandom
