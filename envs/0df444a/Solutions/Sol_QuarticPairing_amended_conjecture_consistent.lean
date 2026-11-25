-- Prove2me | solution 1 for QuarticPairing.amended_conjecture_consistent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:50.506025+00:00
-- url     : https://prove2.me/submissions/a1a08c6b-dd68-42b9-9e27-73eb54edb64c

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
public import Theorems.Thm_QuarticPairing_conjecture12Amended_iff


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ)
    (β : GaussianInt) {κ : ℂ} (hκ : ‖κ‖ = 1)
    (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) :
    Conjecture12Amended g Λ β κ ↔
      ∃ b : ℂ, b ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → ∀ ℓ : ℤ, ℓ ≤ 0 →
        (fun X : ℕ => twistedSum g Λ β X ℓ - amendedMain κ b X ℓ)
          =O[Filter.atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε)) :=
  conjecture12Amended_iff g Λ β hκ h12
end QuarticPairing
