-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.distribution_typeTwist_hasLaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:58:45.499946+00:00
-- url     : https://prove2.me/submissions/79d545db-075c-4449-8962-61f6a06e99ef

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_coordinate_hasLaw


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    (r typeCount ell : Nat)
    [NeZero (ell - 1)]
    (τ : Fin typeCount) :
    ProbabilityTheory.HasLaw
      (fun sample : RandomTwist.Sample r typeCount ell =>
        RandomTwist.typeTwist sample τ)
      (PMF.uniformOfFintype (Fin (ell - 1))).toMeasure
      (RandomTwist.distribution r typeCount ell).toMeasure := by
  exact
    (RandomBase.independentProduct_coordinate_hasLaw
      (RandomTwist.coordinatePMF ell)
      (Sum.inr τ :
        RandomTwist.ChoiceIndex r typeCount))
end QEC.Coding.FiberBundle.TwistGraph
