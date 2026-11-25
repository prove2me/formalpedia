-- Prove2me | solution 1 for QuarticPairing.main_term_one_forced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:43:35.178261+00:00
-- url     : https://prove2.me/submissions/9afa64ec-07f1-4b5b-b363-7489924076db

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
public import Theorems.Thm_QuarticPairing_main_term_forced_of_pairing


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (b b' : ℂ)
    (h0 : ∀ ε : ℝ, 0 < ε → (fun X : ℕ => twistedSum g Λ β X 0 -
      b * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ)) =O[Filter.atTop]
        (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε)))
    (h1 : ∀ ε : ℝ, 0 < ε → (fun X : ℕ => twistedSum g Λ β X 1 -
      b' * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ)) =O[Filter.atTop]
        (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε))) :
    b' = -κ * starRingEnd ℂ b :=
  main_term_forced_of_pairing g Λ β hκ h12 b b' h0 h1
end QuarticPairing
