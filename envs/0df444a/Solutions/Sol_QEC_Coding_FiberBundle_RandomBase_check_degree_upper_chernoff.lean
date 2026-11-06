-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.check_degree_upper_chernoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:49:05.174298+00:00
-- url     : https://prove2.me/submissions/55e70feb-de16-441d-a702-5fc6618e56d8

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
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_mgf_checkDegree_le_poisson

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) (ε t : Real) (ht : 0 ≤ t) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | ε ≤ (checkDegree sample a : Real)} ≤
      Real.exp (-t * ε + (Delta : Real) * (Real.exp t - 1)) := by
  calc
    _ ≤ Real.exp (-t * ε) *
        ProbabilityTheory.mgf
          (fun sample => (checkDegree sample a : Real))
          (distribution r Delta hDelta).toMeasure t := by
      exact ProbabilityTheory.measure_ge_le_exp_mul_mgf ε ht Integrable.of_finite
    _ ≤ Real.exp (-t * ε) *
        Real.exp ((Delta : Real) * (Real.exp t - 1)) := by
      gcongr
      exact mgf_checkDegree_le_poisson r Delta hr hDelta a t
    _ = _ := by rw [← Real.exp_add]
end QEC.Coding.FiberBundle.RandomBase
