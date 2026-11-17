-- Prove2me | solution 1 for Thm61Support.integralValue_neg_of_defined
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:43:27.853785+00:00
-- url     : https://prove2.me/submissions/37511526-95e5-4d42-a14c-458dd8060542

import Theorems.Thm_integralValue_map
import Theorems.Thm_Thm61Support_neg_finset_sum_of_forall_ne_top
import Theorems.Thm_Thm61Support_neg_finset_sum_of_forall_ne_bot
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
    (hXdef : simpleFunctionIntegralDefined μ X) :
    simpleFunctionIntegralValue μ (X.map fun x => -x) =
      -simpleFunctionIntegralValue μ X := by
  classical
  let term : EReal → EReal := fun x => x * (μ (X ⁻¹' {x}) : EReal)
  have hbranch :
      (∀ x ∈ X.range, term x ≠ ⊤) ∨
        (∀ x ∈ X.range, term x ≠ ⊥) := by
    by_cases hpos : simpleFunctionHasPosInf μ X
    · right
      intro x hx hbot
      exact hXdef ⟨hpos, ⟨x, hx, hbot⟩⟩
    · left
      intro x hx htop
      exact hpos ⟨x, hx, htop⟩
  have hnegSum :
      Finset.sum X.range (fun x => -(term x)) = -(Finset.sum X.range term) := by
    rcases hbranch with hnoTop | hnoBot
    · exact neg_finset_sum_of_forall_ne_top X.range term hnoTop
    · exact neg_finset_sum_of_forall_ne_bot X.range term hnoBot
  calc
    simpleFunctionIntegralValue μ (X.map fun x => -x)
        = ∑ x ∈ X.range, -(term x) := by
            simpa [term, simpleFunctionIntegralTerm, neg_mul] using
              (integralValue_map (μ := μ) (g := fun x : EReal => -x) (f := X))
    _ = -∑ x ∈ X.range, term x := by
          exact hnegSum
    _ = -simpleFunctionIntegralValue μ X := by
          simp [simpleFunctionIntegralValue, simpleFunctionIntegralTerm, term]
end Thm61Support

/-  ## Theorem 6.1
Theorem 6.1 at the Definition 6.2 interface.
-/
