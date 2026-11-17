-- Prove2me | solution 1 for Thm61Support.integralValue_add_of_cellwise_distrib
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:42:34.024199+00:00
-- url     : https://prove2.me/submissions/0a6597a7-dd20-4985-9b23-6dec50f73d3f

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
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


theorem solution (μ : Measure Ω) (X Y : SimpleFunc Ω EReal)
    (hcell : simpleFunctionIntegralAddCompatible μ X Y) :
    simpleFunctionIntegralValue μ (X + Y) =
      simpleFunctionIntegralValue μ X + simpleFunctionIntegralValue μ Y := by
  classical
  calc
    simpleFunctionIntegralValue μ (X + Y)
        = ∑ p ∈ (X.pair Y).range,
            (p.1 + p.2) * (μ (X.pair Y ⁻¹' {p}) : EReal) := by
            rw [SimpleFunc.add_eq_map₂]
            simpa using
              (integralValue_map (μ := μ) (g := fun p : EReal × EReal => p.1 + p.2)
                (f := X.pair Y))
    _ = ∑ p ∈ (X.pair Y).range,
          (p.1 * (μ (X.pair Y ⁻¹' {p}) : EReal) +
            p.2 * (μ (X.pair Y ⁻¹' {p}) : EReal)) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          exact hcell p hp
    _ = (∑ p ∈ (X.pair Y).range, p.1 * (μ (X.pair Y ⁻¹' {p}) : EReal)) +
          ∑ p ∈ (X.pair Y).range, p.2 * (μ (X.pair Y ⁻¹' {p}) : EReal) := by
            rw [Finset.sum_add_distrib]
    _ = simpleFunctionIntegralValue μ ((X.pair Y).map Prod.fst) +
          simpleFunctionIntegralValue μ ((X.pair Y).map Prod.snd) := by
          rw [integralValue_map (μ := μ) (g := Prod.fst),
            integralValue_map (μ := μ) (g := Prod.snd)]
    _ = simpleFunctionIntegralValue μ X + simpleFunctionIntegralValue μ Y := by
          simp
end Thm61Support

/-  ## Theorem 6.1
Theorem 6.1 at the Definition 6.2 interface.
-/
