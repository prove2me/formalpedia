-- Prove2me | solution 1 for Thm61Support.integralValue_const_mul_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:43:19.137485+00:00
-- url     : https://prove2.me/submissions/43ce4cc3-8863-4da0-bcd5-dd672259e9ae

import Theorems.Thm_integralValue_map
import Theorems.Thm_Thm61Support_ereal_mul_finset_sum_of_nonneg_of_ne_top
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic
import Theorems.Thm_integralValue_map


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Thm61Support
end Thm61Support
section Thm61Support
open Thm61Support


theorem solution (μ : Measure Ω) (X : SimpleFunc Ω EReal)
    (a : ℝ) (ha : 0 ≤ a) :
    simpleFunctionIntegralValue μ (X.map fun x => (a : EReal) * x) =
      (a : EReal) * simpleFunctionIntegralValue μ X := by
  have haE : 0 ≤ (a : EReal) := by
    exact_mod_cast ha
  have haTop : (a : EReal) ≠ ⊤ := by
    simp
  calc
    simpleFunctionIntegralValue μ (X.map fun x => (a : EReal) * x)
        = ∑ x ∈ X.range, (a : EReal) * (x * (μ (X ⁻¹' {x}) : EReal)) := by
            simpa [simpleFunctionIntegralTerm, mul_assoc] using
              (integralValue_map (μ := μ) (g := fun x : EReal => (a : EReal) * x) (f := X))
    _ = (a : EReal) * ∑ x ∈ X.range, x * (μ (X ⁻¹' {x}) : EReal) := by
          symm
          exact ereal_mul_finset_sum_of_nonneg_of_ne_top X.range haE haTop
            (fun x => x * (μ (X ⁻¹' {x}) : EReal))
    _ = (a : EReal) * simpleFunctionIntegralValue μ X := by
          simp [simpleFunctionIntegralValue, simpleFunctionIntegralTerm]
end Thm61Support

/-  ## Theorem 6.1
Theorem 6.1 at the Definition 6.2 interface.
-/
