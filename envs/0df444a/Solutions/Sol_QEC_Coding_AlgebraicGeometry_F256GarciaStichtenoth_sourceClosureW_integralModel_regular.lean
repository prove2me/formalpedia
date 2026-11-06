-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureW_integralModel_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:17:24.995206+00:00
-- url     : https://prove2.me/submissions/77f95628-cc9b-4dfe-ad10-38f336238451

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinementRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureUnramified
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularRefinement_integralClosure_ramificationIdx_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureW_integralModel_weakDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureW_regularRefinement


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] closureDifferent_modelDedekind closureDifferent_modelFinite
  closureDifferent_modelFraction closureDifferent_modelTorsionFree
variable (m : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (sourceClosureWBase m)] [IsFractionRing A (sourceClosureWBase m)]
    [Algebra A (SourceGaloisClosureField m)]
    [IsScalarTower A (sourceClosureWBase m) (SourceGaloisClosureField m)]
    [Module.IsTorsionFree A (SourceGaloisClosureField m)]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m)))
    (hw : (heightOnePlace (k := F256) (K := SourceGaloisClosureField m) Q).valuation
      (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) = 1) :
    (Q.under A).asIdeal.ramificationIdx' Q.asIdeal = 1 ∧
      multiplicity Q.asIdeal (differentIdeal A (integralClosure A (SourceGaloisClosureField m))) = 0 := by
  have he := RegularRefinement.integralClosure_ramificationIdx_eq_one
    A (sourceClosureWBase m) (SourceGaloisClosureField m) Q
    (sourceClosureW_regularRefinement m (heightOnePlace Q) hw)
  refine ⟨he, ?_⟩
  rw [sourceClosureW_integralModel_weakDifferent m A Q, he]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
