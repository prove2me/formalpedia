-- Prove2me | solution 1 for Rudin.ch06_monotonicity_and_bounds_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T13:08:19.938139+00:00
-- url     : https://prove2.me/submissions/c3c54826-af47-435f-a54c-3e3d8a705a6c

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes
import Theorems.Thm_Rudin_ch06_integral_mono_of_bounded
import Theorems.Thm_Rudin_ch06_abs_integral_le_of_bounded
import Theorems.Thm_Rudin_ch06_integral_additive_of_bounded

open Filter Topology

open Rudin in
/-- Rudin, Theorem 6.12(b), (c), (d), with the boundedness hypotheses of Chapter 6. -/
theorem solution (a b : ℝ) (hab : a ≤ b) (f g α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hf : RSIntegrable a b f α) (hg : RSIntegrable a b g α)
    (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hgb : ∃ M, ∀ x ∈ Set.Icc a b, |g x| ≤ M) :
    ((∀ x ∈ Set.Icc a b, f x ≤ g x) → RSIntegral a b f α ≤ RSIntegral a b g α) ∧
    (∀ c ∈ Set.Icc a b, RSIntegrable a c f α ∧ RSIntegrable c b f α ∧
      RSIntegral a c f α + RSIntegral c b f α = RSIntegral a b f α) ∧
    (∀ M : ℝ, (∀ x ∈ Set.Icc a b, |f x| ≤ M) →
      |RSIntegral a b f α| ≤ M * (α b - α a)) :=
  ⟨fun hfg => ch06_integral_mono_of_bounded a b hab f g α hα hfb hgb hfg,
   ch06_integral_additive_of_bounded a b hab f α hα hfb hf,
   fun M hM => ch06_abs_integral_le_of_bounded a b hab f α hα M hM⟩
