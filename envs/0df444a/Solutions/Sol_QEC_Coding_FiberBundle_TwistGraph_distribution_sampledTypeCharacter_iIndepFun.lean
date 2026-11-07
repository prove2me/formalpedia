-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.distribution_sampledTypeCharacter_iIndepFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:16:01.448291+00:00
-- url     : https://prove2.me/submissions/944dd8a8-3970-4235-959f-f8c52188b3ce

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_distribution_typeTwist_iIndepFun

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    (r typeCount ell : Nat)
    [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell) :
    ProbabilityTheory.iIndepFun
      (fun τ => sampledTypeCharacter frequency τ)
      (RandomTwist.distribution r typeCount ell).toMeasure := by
  exact
    (distribution_typeTwist_iIndepFun r typeCount ell).comp
      (fun _τ shiftIndex =>
        typeCharacterValue frequency shiftIndex)
      (fun _τ => Measurable.of_discrete)
end QEC.Coding.FiberBundle.TwistGraph
