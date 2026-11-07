-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.integral_sampledTypeCharacter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:31:05.78213+00:00
-- url     : https://prove2.me/submissions/cdb13d43-ae21-4696-a900-2ab3e600fbac

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_integral_typeCharacterValue_uniform
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_distribution_typeTwist_hasLaw

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    (r typeCount ell : Nat)
    [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell)
    (hfrequency : frequency ≠ 0)
    (τ : Fin typeCount) :
    ∫ sample,
        sampledTypeCharacter frequency τ sample
      ∂(RandomTwist.distribution r typeCount ell).toMeasure =
      -2 / (ell - 1 : Real) := by
  calc
    _ =
        ∫ shiftIndex,
          typeCharacterValue frequency shiftIndex
        ∂(PMF.uniformOfFintype (Fin (ell - 1))).toMeasure := by
      exact
        (distribution_typeTwist_hasLaw r typeCount ell τ).integral_comp
          ((Measurable.of_discrete :
            Measurable (typeCharacterValue frequency)).aestronglyMeasurable)
    _ = -2 / (ell - 1 : Real) :=
      integral_typeCharacterValue_uniform frequency hfrequency
end QEC.Coding.FiberBundle.TwistGraph
