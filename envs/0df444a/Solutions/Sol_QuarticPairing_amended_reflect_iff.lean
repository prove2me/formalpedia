-- Prove2me | solution 1 for QuarticPairing.amended_reflect_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:40:44.814265+00:00
-- url     : https://prove2.me/submissions/3c15082b-30bb-4d26-8de4-0254914ea3bf

module
public import Definitions.Def_QuarticPairing_Inconsistency
public import Definitions.Def_QuarticPairing_Amended
public import Theorems.Thm_QuarticPairing_isBigO_neg_mul_conj
public import Theorems.Thm_QuarticPairing_amendedMain_reflect
public import Theorems.Thm_QuarticPairing_mul_conj_self_eq_one
public import Theorems.Thm_QuarticPairing_twistedSum_reflect


set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) {κ : ℂ}
    (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (b : ℂ)
    (u : ℕ → ℝ) (ℓ : ℤ) :
    (fun X : ℕ => twistedSum g Λ β X (1 - ℓ) - amendedMain κ b X (1 - ℓ)) =O[atTop] u ↔
      (fun X : ℕ => twistedSum g Λ β X ℓ - amendedMain κ b X ℓ) =O[atTop] u := by
  have he : (fun X : ℕ => twistedSum g Λ β X (1 - ℓ) - amendedMain κ b X (1 - ℓ)) =
      fun X => -κ * starRingEnd ℂ (twistedSum g Λ β X ℓ - amendedMain κ b X ℓ) := by
    funext X
    rw [twistedSum_reflect g Λ β hκ h12 X ℓ, amendedMain_reflect hκ b X ℓ, map_sub]
    ring
  rw [he]
  constructor
  · intro h
    have := isBigO_neg_mul_conj hκ h
    refine this.congr_left fun X => ?_
    have hκκ := mul_conj_self_eq_one hκ
    simp only [map_mul, map_neg, Complex.conj_conj]
    linear_combination (twistedSum g Λ β X ℓ - amendedMain κ b X ℓ) * hκκ
  · exact isBigO_neg_mul_conj hκ
end QuarticPairing
