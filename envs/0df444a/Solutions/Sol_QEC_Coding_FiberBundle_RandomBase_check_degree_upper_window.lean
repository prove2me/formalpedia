-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.check_degree_upper_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:51:01.163202+00:00
-- url     : https://prove2.me/submissions/59cf7933-856f-4a9a-9220-12c6043c780a

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
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_check_degree_upper_chernoff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | (101 * (Delta : Real) / 100) ≤ checkDegree sample a} ≤
      Real.exp (-(Delta : Real) / 40000) := by
  calc
    _ ≤ Real.exp
        (-(1 / 200 : Real) * (101 * (Delta : Real) / 100) +
          (Delta : Real) * (Real.exp (1 / 200 : Real) - 1)) :=
      check_degree_upper_chernoff r Delta hr hDelta a _ _ (by norm_num)
    _ ≤ Real.exp (-(Delta : Real) / 40000) := by
      apply Real.exp_le_exp_of_le
      have he := exp_sub_one_le_add_sq (t := (1 / 200 : Real)) (by norm_num)
      calc
        _ ≤ -(1 / 200 : Real) * (101 * (Delta : Real) / 100) +
            (Delta : Real) * ((1 / 200 : Real) + (1 / 200 : Real) ^ 2) := by
          gcongr
        _ = _ := by ring
end QEC.Coding.FiberBundle.RandomBase
