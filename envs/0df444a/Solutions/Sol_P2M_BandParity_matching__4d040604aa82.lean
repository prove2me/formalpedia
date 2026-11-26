-- Prove2me | solution 1 for P2M_BandParity_matching__4d040604aa82
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:00.475356+00:00
-- url     : https://prove2.me/submissions/145b511e-fbe2-474b-a0d7-e576d555f031

module
public import Mathlib
public import Definitions.Def_BandParity_Matching
public import Theorems.Thm_BandParity_sum_sign_mul_modEq

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
namespace BandParity
theorem _root_.solution {ι κ : Type*} (X : Finset ι) (Y : Finset κ) (π : ι → κ)
    (hπ : Set.BijOn π X Y) (σ : ι → ℤ) (τ : κ → ℤ)
    (hσ : ∀ x ∈ X, σ x = 1 ∨ σ x = -1) (hτ : ∀ y ∈ Y, τ y = 1 ∨ τ y = -1) :
    ∑ x ∈ X, σ x * τ (π x) ≡ ∑ x ∈ X, σ x + ∑ y ∈ Y, τ y - X.card [ZMOD 4] := by
  have hY : ∑ x ∈ X, τ (π x) = ∑ y ∈ Y, τ y :=
    Finset.sum_nbij π (fun x hx => hπ.mapsTo hx) (fun x hx y hy h => hπ.injOn hx hy h)
      (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := hπ.surjOn hy
        exact ⟨x, hx, rfl⟩) (fun _ _ => rfl)
  rw [← hY]
  exact sum_sign_mul_modEq X σ (fun x => τ (π x)) hσ (fun x hx => hτ _ (hπ.mapsTo hx))
end BandParity
