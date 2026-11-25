-- Prove2me | solution 1 for QuarticPairing.not_conjecture12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:41:46.077918+00:00
-- url     : https://prove2.me/submissions/2bf34bc8-a83c-4484-9734-886070b394a2

module
public import Definitions.Def_QuarticPairing_Pairing
public import Definitions.Def_QuarticPairing_Inconsistency
public import Theorems.Thm_QuarticPairing_not_conjecture12_aux
public import Theorems.Thm_QuarticPairing_twistedSum_one


set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) {κ : ℂ}
    (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) :
    ¬ Conjecture12 g Λ β := by
  refine not_conjecture12_aux g Λ β fun h1 => IsBigO.of_norm_left ?_
  have : (fun X : ℕ => ‖twistedSum g Λ β X 0‖) = fun X => ‖twistedSum g Λ β X 1‖ := by
    funext X
    rw [twistedSum_one g Λ β hκ h12 X, norm_mul, norm_neg, hκ, one_mul, Complex.norm_conj]
  rw [this]; exact h1
end QuarticPairing
