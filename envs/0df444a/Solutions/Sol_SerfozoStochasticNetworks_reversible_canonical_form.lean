-- Prove2me | solution 1 for SerfozoStochasticNetworks.reversible_canonical_form
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T21:44:31.547043+00:00
-- url     : https://prove2.me/submissions/86f5d46f-5a98-466a-8522-ea965c2b2a33

import Mathlib
import Definitions.Def_SerfozoStochasticNetworks_Reversible

namespace SerfozoStochasticNetworks

end SerfozoStochasticNetworks

open SerfozoStochasticNetworks
theorem solution {E : Type*} (q : E → E → ℝ) (π : E → ℝ)
    (hq : ∀ x y, 0 ≤ q x y) (hπ : ∀ x, 0 < π x) :
    DetailedBalance q π ↔ ∃ γ : E → E → ℝ, (∀ x y, 0 ≤ γ x y) ∧ (∀ x y, γ x y = γ y x) ∧
      ∀ x y, q x y = γ x y / π x := by
  constructor
  · intro hdb
    refine ⟨fun x y => π x * q x y, fun x y => mul_nonneg (le_of_lt (hπ x)) (hq x y),
      fun x y => hdb x y, fun x y => ?_⟩
    rw [mul_div_cancel_left₀]
    exact (hπ x).ne'
  · rintro ⟨γ, hγ0, hγsym, hγq⟩ x y
    rw [hγq x y, hγq y x, hγsym y x, mul_div_cancel₀ _ (hπ x).ne', mul_div_cancel₀ _ (hπ y).ne']

