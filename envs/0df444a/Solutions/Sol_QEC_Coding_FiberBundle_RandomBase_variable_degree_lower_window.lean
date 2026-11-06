-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.variable_degree_lower_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:51:24.791567+00:00
-- url     : https://prove2.me/submissions/27a4a9e8-6249-4a33-921b-dc2b321bf4a0

import Definitions.Def_QEC_Coding_FiberBundle_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exp_sub_one_le_add_sq
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_variable_degree_lower_chernoff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | (variableDegree sample b : Real) ≤ 74 * Delta / 100} ≤
      Real.exp (-(Delta : Real) / 32000) := by
  calc
    _ ≤ Real.exp
        (-(-1 / 200 : Real) * (74 * (Delta : Real) / 100) +
          (3 * (Delta : Real) / 4) * (Real.exp (-1 / 200 : Real) - 1)) :=
      variable_degree_lower_chernoff r Delta hr hDelta b _ _ (by norm_num)
    _ ≤ Real.exp (-(Delta : Real) / 32000) := by
      apply Real.exp_le_exp_of_le
      have he := exp_sub_one_le_add_sq (t := (-1 / 200 : Real)) (by norm_num)
      calc
        _ ≤ -(-1 / 200 : Real) * (74 * (Delta : Real) / 100) +
            (3 * (Delta : Real) / 4) *
              ((-1 / 200 : Real) + (-1 / 200 : Real) ^ 2) := by
          gcongr
        _ = _ := by ring
end QEC.Coding.FiberBundle.RandomBase
