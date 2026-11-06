-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.exp_sub_one_le_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:29:38.054519+00:00
-- url     : https://prove2.me/submissions/8f587ca9-99e5-4315-869c-69a1d48e34da

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
theorem _root_.solution {t : Real} (ht : |t| ≤ 1) :
    Real.exp t - 1 ≤ t + t ^ 2 := by
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le ht)).2
  linarith
end QEC.Coding.FiberBundle.RandomBase
