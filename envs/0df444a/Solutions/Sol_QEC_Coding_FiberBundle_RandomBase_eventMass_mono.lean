-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.eventMass_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:56:17.429888+00:00
-- url     : https://prove2.me/submissions/d27ba3ee-a187-4d77-9878-e54d66ab50f6

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_eq_toMeasure


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (left right : Ω → Prop)
    [DecidablePred left] [DecidablePred right]
    (h : ∀ ω, left ω → right ω) :
    eventMass p left ≤ eventMass p right := by
  rw [eventMass_eq_toMeasure, eventMass_eq_toMeasure]
  exact measure_mono h
end QEC.Coding.FiberBundle.RandomBase
