-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.HasDependencyGraph.factor_avoid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:41:02.23545+00:00
-- url     : https://prove2.me/submissions/c0e54eb6-a8cc-49a2-b2e5-e2ea0037471d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
namespace QEC.Coding.ProbabilisticConstruction
namespace HasDependencyGraph
theorem _root_.solution {μ : Measure Ω} {B : I → Set Ω}
    {G : SimpleGraph I} (h : HasDependencyGraph μ B G) (i : I) (S : Finset I)
    (hS : ∀ j ∈ S, j ≠ i ∧ ¬ G.Adj i j) :
    μ.real (B i ∩ avoid B S) = μ.real (B i) * μ.real (avoid B S) := by
  have hleft : MeasurableSet[MeasurableSpace.generateFrom {B i}] (B i) :=
    MeasurableSpace.measurableSet_generateFrom (by simp)
  have hright : MeasurableSet[MeasurableSpace.generateFrom
      {E | ∃ j, j ≠ i ∧ ¬ G.Adj i j ∧ E = B j}] (avoid B S) := by
    revert hS
    induction S using Finset.induction_on with
    | empty => intro hS; simp
    | @insert j S hj ih =>
      intro hS
      rw [avoid_insert]
      exact (ih (fun k hk => hS k (Finset.mem_insert_of_mem hk))).diff
        (MeasurableSpace.measurableSet_generateFrom
          ⟨j, (hS j (Finset.mem_insert_self _ _)).1,
            (hS j (Finset.mem_insert_self _ _)).2, rfl⟩)
  have hf := ((h i).indepSet_of_measurableSet hleft hright).measure_inter_eq_mul
  simpa only [Measure.real, ENNReal.toReal_mul] using congrArg ENNReal.toReal hf
end HasDependencyGraph
end QEC.Coding.ProbabilisticConstruction
