-- Prove2me | solution 1 for QuarticPairing.pairing_of_twists_defect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:42:20.317601+00:00
-- url     : https://prove2.me/submissions/5c09517f-5070-4390-bebc-d6e3305d386c

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
public import Theorems.Thm_QuarticPairing_twistedSum_one_sub


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (E : GaussianInt → Prop)
    (h12 : ∀ c, ¬ E c → Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ) :
    ‖twistedSum g Λ β X 1 + κ * starRingEnd ℂ (twistedSum g Λ β X 0)‖ ≤
      2 * defectSum g Λ β E X :=
  twistedSum_one_sub g Λ β hκ E h12 X
end QuarticPairing
