-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomTwist.distribution_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:36:41.497029+00:00
-- url     : https://prove2.me/submissions/e6897b3e-f220-464f-9665-95fc52db0e80

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomTwist
open scoped BigOperators
namespace QEC.Coding.FiberBundle.RandomTwist
theorem _root_.solution
    (r typeCount ell : Nat)
    [NeZero (ell - 1)]
    (sample : Sample r typeCount ell) :
    distribution r typeCount ell sample =
      ∏ i : ChoiceIndex r typeCount,
        coordinatePMF ell i (sample i) := by
  rfl
end QEC.Coding.FiberBundle.RandomTwist
