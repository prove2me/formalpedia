-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.map_maximalIdeal_eq_span_sourceStepIntegralUniformizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:48:16.362906+00:00
-- url     : https://prove2.me/submissions/a9fb11d6-bdf5-4ba1-9771-8d6f72ebb833

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Ideal.map (algebraMap P.valuationRing (SourceStepIntegralClosure P x hx))
        (IsLocalRing.maximalIdeal P.valuationRing) =
      Ideal.span ({sourceStepIntegralUniformizer P x hx} :
        Set (SourceStepIntegralClosure P x hx)) := by
  rw [maximalIdeal_eq_span_reciprocalUniformizer P
      (sourceStepRhs x) (sourceStepRhs_order P x hx),
    Ideal.map_span, Set.image_singleton]
  change Ideal.span
      ({algebraMap P.valuationRing (SourceStepIntegralClosure P x hx)
        (sourceStepUniformizer P x hx)} :
        Set (SourceStepIntegralClosure P x hx)) = _
  rw [algebraMap_sourceStepUniformizer]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
