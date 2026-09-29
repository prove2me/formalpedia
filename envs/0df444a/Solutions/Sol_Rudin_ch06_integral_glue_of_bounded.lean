-- Prove2me | solution 1 for Rudin.ch06_integral_glue_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T14:54:35.010632+00:00
-- url     : https://prove2.me/submissions/e50d9ed1-792a-488a-b621-eb93a1248976

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes
import Theorems.Thm_Rudin_ch06_upper_lower_integral_additive

open Filter Topology

open Rudin in
/-- Converse of Rudin, Theorem 6.12(c): integrability on `[a, c]` and on `[c, b]` glues to
integrability on `[a, b]`, with additive integrals. -/
theorem solution (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    (h₁ : RSIntegrable a c f α) (h₂ : RSIntegrable c b f α) :
    RSIntegrable a b f α ∧
      RSIntegral a c f α + RSIntegral c b f α = RSIntegral a b f α := by
  obtain ⟨hU, hL⟩ := ch06_upper_lower_integral_additive a c b hac hcb f α hα hfb
  have hInt : RSIntegrable a b f α := by
    show upperIntegral a b f α = lowerIntegral a b f α
    rw [hU, hL, h₁, h₂]
  exact ⟨hInt, hU.symm⟩
