-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWSeed_normalizedRefinement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:34:28.968441+00:00
-- url     : https://prove2.me/submissions/bfaa5e74-b402-45e7-a7ea-de97c924a68d

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalTraceSeed
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWFieldGenerator_order_dichotomy
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_artinSchreier16_bottom_normalizedRefinement


set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A SourceGaloisWField] [IsFractionRing A SourceGaloisWField]
    [Algebra A (RatFunc F256)] [IsScalarTower A SourceGaloisWField (RatFunc F256)]
    [Module.Finite A (integralClosure A (RatFunc F256))]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (RatFunc F256))) :
    NormalizedRefinement A SourceGaloisWField (RatFunc F256) Q ⊥ ⊤ := by
  have h := artinSchreier16_bottom_normalizedRefinement A SourceGaloisWField
    (RatFunc F256) Q sourceGaloisWFieldGenerator RatFunc.X rfl
    sourceGaloisWFieldGenerator_order_dichotomy
  have htop : SourceGaloisWField⟮(RatFunc.X : RatFunc F256)⟯ = ⊤ :=
    IntermediateField.adjoin_eq_top_of_adjoin_eq_top F256 RatFunc.adjoin_X
  rwa [htop] at h
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
