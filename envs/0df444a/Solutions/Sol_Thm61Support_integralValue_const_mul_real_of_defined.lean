-- Prove2me | solution 1 for Thm61Support.integralValue_const_mul_real_of_defined
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:46:30.997746+00:00
-- url     : https://prove2.me/submissions/5545b865-6109-443d-8a4b-811b6eec2c0f

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic
import Theorems.Thm_Thm61Support_integralValue_const_mul_of_nonneg
import Theorems.Thm_Thm61Support_integralValue_neg_of_defined


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
    (α : ℝ) (hXdef : simpleFunctionIntegralDefined μ X) :
    simpleFunctionIntegralValue μ (X.map fun x => (α : EReal) * x) =
      (α : EReal) * simpleFunctionIntegralValue μ X := by
  by_cases hα : 0 ≤ α
  · exact integralValue_const_mul_of_nonneg μ X α hα
  · have hneg : 0 ≤ -α := by linarith
    calc
      simpleFunctionIntegralValue μ (X.map fun x => (α : EReal) * x)
          = simpleFunctionIntegralValue μ
              ((X.map fun x => -x).map fun x => ((-α : ℝ) : EReal) * x) := by
                congr 1
                ext ω
                simp [SimpleFunc.map_map]
      _ = (((-α : ℝ) : EReal) * simpleFunctionIntegralValue μ (X.map fun x => -x)) := by
            exact integralValue_const_mul_of_nonneg μ (X.map fun x => -x) (-α) hneg
      _ = (((-α : ℝ) : EReal) * (-simpleFunctionIntegralValue μ X)) := by
            rw [integralValue_neg_of_defined (μ := μ) (X := X) hXdef]
      _ = (α : EReal) * simpleFunctionIntegralValue μ X := by
            simp
end Thm61Support

/-  ## Theorem 6.1
Theorem 6.1 at the Definition 6.2 interface.
-/
