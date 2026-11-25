-- Prove2me | solution 1 for QuarticPairing.conjecture12_inconsistent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:43:44.057934+00:00
-- url     : https://prove2.me/submissions/5685964e-5783-4c43-9cee-011ed6ddddfc

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
public import Theorems.Thm_QuarticPairing_not_conjecture12


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) :
    ¬ Conjecture12 g Λ β :=
  not_conjecture12 g Λ β hκ h12
end QuarticPairing
