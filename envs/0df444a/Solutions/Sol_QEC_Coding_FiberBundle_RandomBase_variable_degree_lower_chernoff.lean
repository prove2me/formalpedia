-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.variable_degree_lower_chernoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:49:18.147293+00:00
-- url     : https://prove2.me/submissions/2901b89d-4ec9-4b34-aab5-606894e541fd

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
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_mgf_variableDegree_le_poisson

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) (ε t : Real) (ht : t ≤ 0) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | (variableDegree sample b : Real) ≤ ε} ≤
      Real.exp
        (-t * ε + (3 * (Delta : Real) / 4) * (Real.exp t - 1)) := by
  calc
    _ ≤ Real.exp (-t * ε) *
        ProbabilityTheory.mgf
          (fun sample => (variableDegree sample b : Real))
          (distribution r Delta hDelta).toMeasure t := by
      exact ProbabilityTheory.measure_le_le_exp_mul_mgf ε ht Integrable.of_finite
    _ ≤ Real.exp (-t * ε) *
        Real.exp ((3 * (Delta : Real) / 4) * (Real.exp t - 1)) := by
      gcongr
      exact mgf_variableDegree_le_poisson r Delta hr hDelta b t
    _ = _ := by rw [← Real.exp_add]
end QEC.Coding.FiberBundle.RandomBase
