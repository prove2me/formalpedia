-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.independentProduct_coordinate_hasLaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:35:10.603082+00:00
-- url     : https://prove2.me/submissions/d2ba4812-396e-4e99-8287-381c2bd5c3c8

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
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_toMeasure_eq_pi

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type u} [∀ i, Fintype (κ i)]
    [∀ i, MeasurableSpace (κ i)]
    [∀ i, MeasurableSingletonClass (κ i)]
    (p : ∀ i, PMF (κ i)) (i : ι) :
    ProbabilityTheory.HasLaw
      (fun x => x i) (p i).toMeasure (independentProduct p).toMeasure := by
  rw [independentProduct_toMeasure_eq_pi p]
  exact (MeasureTheory.measurePreserving_eval
    (fun i => (p i).toMeasure) i).hasLaw
end QEC.Coding.FiberBundle.RandomBase
