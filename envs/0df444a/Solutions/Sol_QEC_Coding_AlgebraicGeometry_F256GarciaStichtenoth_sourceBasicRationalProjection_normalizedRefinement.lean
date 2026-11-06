-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicRationalProjection_normalizedRefinement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:27:11.819987+00:00
-- url     : https://prove2.me/submissions/6e0ac9c3-84d5-46b1-8ca0-8a26dc930141

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionFields
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_artinSchreier16_bottom_normalizedRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicRationalSubfield_sourceStepRhs_order_dichotomy


set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
variable {E : Type*} [_root_.Field E] [Algebra F256 E]
    (x : E) (hx : Transcendental F256 x) (y : E)
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A F256⟮x⟯] [IsFractionRing A F256⟮x⟯]
    [Algebra A E] [IsScalarTower A F256⟮x⟯ E]
    [FiniteDimensional F256⟮x⟯ E] [Algebra.IsSeparable F256⟮x⟯ E]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
include hx
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (hy : y ^ 16 + y = algebraMap F256⟮x⟯ E
      (sourceStepRhs (AdjoinSimple.gen F256 x))) :
    NormalizedRefinement A F256⟮x⟯ E Q ⊥ (F256⟮x⟯)⟮y⟯ :=
  artinSchreier16_bottom_normalizedRefinement A F256⟮x⟯ E Q
    (sourceStepRhs (AdjoinSimple.gen F256 x)) y hy
    (sourceBasicRationalSubfield_sourceStepRhs_order_dichotomy x hx)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
