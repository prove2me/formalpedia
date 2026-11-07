-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.two_mul_ell_mul_exp_neg_typeCount_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:58:54.418105+00:00
-- url     : https://prove2.me/submissions/f343b6c6-8604-4700-a30b-d896ef527fcc

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    (typeCount ell : Nat)
    (hEll : 100001 ≤ ell)
    (hTypeCount :
      (40000000000 : Real) * Real.log (ell : Real) ≤
        (typeCount : Real)) :
    2 * ell *
        Real.exp (-(typeCount : Real) / 20000000000) <
      1 := by
  have hEllPos : (0 : Real) < ell := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 100001) hEll)
  have hExponent :
      -(typeCount : Real) / 20000000000 ≤
        -2 * Real.log (ell : Real) := by
    linarith
  calc
    2 * ell *
        Real.exp (-(typeCount : Real) / 20000000000) ≤
        2 * ell * Real.exp (-2 * Real.log (ell : Real)) := by
      gcongr
    _ = 2 / (ell : Real) := by
      rw [show -2 * Real.log (ell : Real) =
          -(Real.log (ell : Real) + Real.log (ell : Real)) by ring,
        Real.exp_neg, Real.exp_add, Real.exp_log hEllPos]
      field_simp [hEllPos.ne']
    _ < 1 := by
      rw [div_lt_one hEllPos]
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 2 < 100001) hEll)
end QEC.Coding.FiberBundle.TwistGraph
