-- Prove2me | solution 1 for QuarticPairing.conjecture12Amended_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:42:53.813534+00:00
-- url     : https://prove2.me/submissions/ac238ff1-4d87-4d8a-8046-3b62868af16b

module
public import Definitions.Def_QuarticPairing_Inconsistency
public import Definitions.Def_QuarticPairing_Amended
public import Theorems.Thm_QuarticPairing_amended_reflect_iff

set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) :
    Conjecture12Amended g Λ β κ ↔
      ∃ b : ℂ, b ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → ∀ ℓ : ℤ, ℓ ≤ 0 →
        (fun X : ℕ => twistedSum g Λ β X ℓ - amendedMain κ b X ℓ)
          =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε)) := by
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, fun ε hε ℓ _ => h ε hε ℓ⟩
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, fun ε hε ℓ => ?_⟩
    by_cases hℓ : ℓ ≤ 0
    · exact h ε hε ℓ hℓ
    · have := (amended_reflect_iff g Λ β hκ h12 b _ (1 - ℓ)).2 (h ε hε (1 - ℓ) (by omega))
      rwa [sub_sub_cancel] at this
end QuarticPairing
