-- Prove2me | solution 1 for QuarticPairing.pairing_of_twists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:41:48.647429+00:00
-- url     : https://prove2.me/submissions/ede66cd1-f507-46b9-8112-313b7c57d444

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
public import Theorems.Thm_QuarticPairing_twistedSum_one


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) {κ : ℂ}
    (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ) :
    twistedSum g Λ β X 1 = -κ * starRingEnd ℂ (twistedSum g Λ β X 0) :=
  twistedSum_one g Λ β hκ h12 X
end QuarticPairing
