-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.eventMass_le_sum_eventMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:56:06.162915+00:00
-- url     : https://prove2.me/submissions/a1ce2357-acdb-4e60-9a13-cb1e7e53a9d4

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_eq_toMeasure


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (event : Ω → Prop) [DecidablePred event]
    (cover : ι → Ω → Prop) [∀ i, DecidablePred (cover i)]
    (hcover : ∀ ω, event ω → ∃ i, cover i ω) :
    eventMass p event ≤ ∑ i, eventMass p (cover i) := by
  rw [eventMass_eq_toMeasure]
  calc
    _ ≤ p.toMeasure (⋃ i, {ω | cover i ω}) := by
      apply measure_mono
      intro ω hω
      rcases hcover ω hω with ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    _ ≤ ∑' i, p.toMeasure {ω | cover i ω} := measure_iUnion_le _
    _ = ∑ i, eventMass p (cover i) := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro i _hi
      exact (eventMass_eq_toMeasure p (cover i)).symm
end QEC.Coding.FiberBundle.RandomBase
