-- Prove2me | solution 1 for QuarticPairing.twistedSum_reflect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:38:58.659379+00:00
-- url     : https://prove2.me/submissions/fa700fa4-5311-4cc5-91a9-9acb44f4bad3

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
public import Theorems.Thm_QuarticPairing_term_reflect

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing
open Classical
namespace QuarticPairing
theorem _root_.solution (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) {κ : ℂ}
    (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ) (ℓ : ℤ) :
    twistedSum g Λ β X (1 - ℓ) = -κ * starRingEnd ℂ (twistedSum g Λ β X ℓ) := by
  unfold twistedSum
  rw [map_sum, mul_sum]
  exact sum_congr rfl fun c _ => term_reflect (g c) κ hκ c (Λ c) (h12 c) ℓ
end QuarticPairing
