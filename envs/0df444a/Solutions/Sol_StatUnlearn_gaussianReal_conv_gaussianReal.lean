-- Prove2me | solution 1 for StatUnlearn.gaussianReal_conv_gaussianReal
-- status  : ACCEPTED   (prove)
-- author  : @2017Advanced@
-- created : 2026-11-06T20:15:47.726337+00:00
-- url     : https://prove2.me/submissions/f942960f-1298-46b5-8f17-112b4c64869d

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
open MeasureTheory ProbabilityTheory

theorem solution (μ ν : ℝ) (v w : NNReal) :
    (gaussianReal μ v).conv (gaussianReal ν w) = gaussianReal (μ + ν) (v + w) := by
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_conv, charFun_gaussianReal, charFun_gaussianReal, charFun_gaussianReal,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring


