-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.degreeWindows_failureMass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:52:01.355199+00:00
-- url     : https://prove2.me/submissions/bde8157c-c15f-4a31-b34b-ffa18be267c2

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
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_degreeWindows_failure_measure_le
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_failureMass_eq_toMeasure

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r) :
    @failureMass
        (Sample r)
        inferInstance
        (distribution r Delta hDelta)
        (fun sample => HasDegreeWindows (Delta := Delta) sample)
        (Classical.decPred _) ≤
      ENNReal.ofReal
        ((14 * r : Real) * Real.exp (-(Delta : Real) / 40000)) := by
  classical
  rw [failureMass_eq_toMeasure]
  rw [← ofReal_measureReal (μ := (distribution r Delta hDelta).toMeasure)
    (s := {sample | ¬HasDegreeWindows (Delta := Delta) sample})]
  exact ENNReal.ofReal_le_ofReal
    (degreeWindows_failure_measure_le r Delta hr hDelta)
end QEC.Coding.FiberBundle.RandomBase
