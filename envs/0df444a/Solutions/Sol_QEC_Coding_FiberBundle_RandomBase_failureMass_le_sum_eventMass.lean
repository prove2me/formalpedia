-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.failureMass_le_sum_eventMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:30:02.274199+00:00
-- url     : https://prove2.me/submissions/232fb283-dbe5-4716-a2c1-70b8b6b25c5e

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_eq_toMeasure
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_failureMass_eq_toMeasure


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (event : Ω → Prop) [DecidablePred event]
    (bad : ι → Ω → Prop) [∀ i, DecidablePred (bad i)]
    (hcover : ∀ ω, ¬event ω → ∃ i, bad i ω) :
    failureMass p event ≤ ∑ i, eventMass p (bad i) := by
  rw [failureMass_eq_toMeasure]
  calc
    _ ≤ p.toMeasure (⋃ i, {ω | bad i ω}) := by
      apply measure_mono
      intro ω hω
      rcases hcover ω hω with ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    _ ≤ ∑' i, p.toMeasure {ω | bad i ω} := measure_iUnion_le _
    _ = ∑ i, eventMass p (bad i) := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro i _hi
      exact (eventMass_eq_toMeasure p (bad i)).symm
end QEC.Coding.FiberBundle.RandomBase
