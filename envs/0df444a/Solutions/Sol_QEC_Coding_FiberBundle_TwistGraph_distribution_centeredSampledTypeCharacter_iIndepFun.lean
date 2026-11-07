-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.distribution_centeredSampledTypeCharacter_iIndepFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:20:11.849204+00:00
-- url     : https://prove2.me/submissions/b2bc4273-e814-42a8-8cb3-f225e272bd61

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_distribution_sampledTypeCharacter_iIndepFun

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
      (fun τ => centeredSampledTypeCharacter frequency τ)
      (RandomTwist.distribution r typeCount ell).toMeasure := by
  exact
    (distribution_sampledTypeCharacter_iIndepFun
      r typeCount ell frequency).comp
      (fun _τ x => x - (-2 / (ell - 1 : Real)))
      (fun _τ => by fun_prop)
end QEC.Coding.FiberBundle.TwistGraph
