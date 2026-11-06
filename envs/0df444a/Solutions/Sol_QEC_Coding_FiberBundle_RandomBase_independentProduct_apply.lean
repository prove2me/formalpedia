-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:28:56.59571+00:00
-- url     : https://prove2.me/submissions/abe38ea0-37ab-4811-99ad-9df14965b3ce

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
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type u} [∀ i, Fintype (κ i)]
    (p : ∀ i, PMF (κ i)) (x : ∀ i, κ i) :
    independentProduct p x = ∏ i, p i (x i) := by
  rfl
end QEC.Coding.FiberBundle.RandomBase
