-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.eventMass_decidable_irrel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:30:01.378766+00:00
-- url     : https://prove2.me/submissions/989f70cf-9aa4-4c66-bd64-321acbdf5972

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {Ω : Type*} [Fintype Ω]
    (p : PMF Ω) (event : Ω → Prop)
    (d₁ d₂ : DecidablePred event) :
    @eventMass Ω inferInstance p event d₁ =
      @eventMass Ω inferInstance p event d₂ := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  rw [hd]
end QEC.Coding.FiberBundle.RandomBase
