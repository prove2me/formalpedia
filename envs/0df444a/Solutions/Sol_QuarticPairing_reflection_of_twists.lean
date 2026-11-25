-- Prove2me | solution 1 for QuarticPairing.reflection_of_twists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:40:46.091269+00:00
-- url     : https://prove2.me/submissions/25effb91-715e-4e58-8fb0-527ec3ddace8

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
public import Theorems.Thm_QuarticPairing_twistedSum_reflect


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ)
    (ℓ : ℤ) :
    twistedSum g Λ β X (1 - ℓ) = -κ * starRingEnd ℂ (twistedSum g Λ β X ℓ) :=
  twistedSum_reflect g Λ β hκ h12 X ℓ
end QuarticPairing
