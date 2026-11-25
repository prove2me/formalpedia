-- Prove2me | solution 1 for QuarticPairing.twistedSum_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:40:41.711567+00:00
-- url     : https://prove2.me/submissions/ddf12619-5f30-4429-b9a8-35f5d36b1279

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
public import Theorems.Thm_QuarticPairing_term_one_add

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing
open Classical
namespace QuarticPairing
theorem _root_.solution (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) {κ : ℂ}
    (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ) :
    twistedSum g Λ β X 1 = -κ * starRingEnd ℂ (twistedSum g Λ β X 0) := by
  rw [← sub_eq_zero, show ∀ a b : ℂ, a - -κ * b = a + κ * b from fun a b => by ring]
  unfold twistedSum
  rw [map_sum, mul_sum, ← sum_add_distrib]
  exact sum_eq_zero fun c _ => term_one_add (g c) κ hκ c (Λ c) (h12 c)
end QuarticPairing
