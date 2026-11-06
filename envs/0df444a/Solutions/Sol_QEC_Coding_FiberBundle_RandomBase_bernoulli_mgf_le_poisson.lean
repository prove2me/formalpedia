-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.bernoulli_mgf_le_poisson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:31:48.83443+00:00
-- url     : https://prove2.me/submissions/475a1fca-40ff-406e-bcd5-271ad46ce0db

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

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (t : Real) :
    (1 - (incidenceProbability (4 * r) Delta).toReal) +
        (incidenceProbability (4 * r) Delta).toReal * Real.exp t ≤
      Real.exp
        ((incidenceProbability (4 * r) Delta).toReal *
          (Real.exp t - 1)) := by
  calc
    _ = (incidenceProbability (4 * r) Delta).toReal *
          (Real.exp t - 1) + 1 := by ring
    _ ≤ _ := Real.add_one_le_exp _
end QEC.Coding.FiberBundle.RandomBase
