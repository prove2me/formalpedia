-- Prove2me | solution 1 for P2M_BandParity_matching_indep__280075205c52
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:59:14.63812+00:00
-- url     : https://prove2.me/submissions/7c505c6d-9d3a-4e65-a9cd-8bccd1aefa3a

module
public import Mathlib
public import Definitions.Def_BandParity_Matching
public import Theorems.Thm_P2M_BandParity_matching__4d040604aa82

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
namespace BandParity
theorem _root_.solution {ι κ : Type*} (X : Finset ι) (Y : Finset κ) (π π' : ι → κ)
    (hπ : Set.BijOn π X Y) (hπ' : Set.BijOn π' X Y) (σ : ι → ℤ) (τ : κ → ℤ)
    (hσ : ∀ x ∈ X, σ x = 1 ∨ σ x = -1) (hτ : ∀ y ∈ Y, τ y = 1 ∨ τ y = -1) :
    ∑ x ∈ X, σ x * τ (π x) ≡ ∑ x ∈ X, σ x * τ (π' x) [ZMOD 4] :=
  (matching' X Y π hπ σ τ hσ hτ).trans (matching' X Y π' hπ' σ τ hσ hτ).symm
end BandParity
