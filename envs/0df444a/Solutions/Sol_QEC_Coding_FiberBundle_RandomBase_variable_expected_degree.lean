-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.variable_expected_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:35:22.019972+00:00
-- url     : https://prove2.me/submissions/733404d6-5352-4a90-9097-c5f8012a9c2d

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
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_check_expected_degree

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r) :
    ((3 * r : Nat) : Real) *
        (incidenceProbability (4 * r) Delta).toReal =
      3 * (Delta : Real) / 4 := by
  rw [← check_expected_degree r Delta hr]
  push_cast
  field_simp
end QEC.Coding.FiberBundle.RandomBase
