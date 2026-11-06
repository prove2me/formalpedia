-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicReverse_normalizedRefinement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:32:38.264642+00:00
-- url     : https://prove2.me/submissions/d09dc9d4-2c16-480e-b196-3c03600c0452

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionFields
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_adjoin_simple_gen_eq_top
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_artinSchreier16_bottom_normalizedRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicRationalSubfield_sourceStepRhs_order_dichotomy
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicSourceCoordinate_transcendental


set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (i : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (SourceBasicReverseField i)] [IsFractionRing A (SourceBasicReverseField i)]
    [Algebra A (SourceBasicReverseExtensionField i)]
    [IsScalarTower A (SourceBasicReverseField i) (SourceBasicReverseExtensionField i)]
    [Module.Finite A (integralClosure A (SourceBasicReverseExtensionField i))]
    (Q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure A (SourceBasicReverseExtensionField i))) :
    NormalizedRefinement A (SourceBasicReverseField i) (SourceBasicReverseExtensionField i)
      Q ⊥ ⊤ := by
  let x := (sourceDistinguishedCoordinate (i + 1))⁻¹
  have hx : Transcendental F256 x := by
    intro halg
    exact sourceBasicSourceCoordinate_transcendental (i + 1) (IsAlgebraic.inv_iff.mp halg)
  let y := AdjoinSimple.gen (SourceBasicReverseField i)
    (sourceRecursionEmbedding i ((sourceDistinguishedCoordinate i)⁻¹))
  have hy : y ^ 16 + y = algebraMap (SourceBasicReverseField i)
      (SourceBasicReverseExtensionField i) (sourceStepRhs (AdjoinSimple.gen F256 x)) := by
    apply Subtype.ext
    exact sourceBasicReverse_root_equation i
  have h := artinSchreier16_bottom_normalizedRefinement A (SourceBasicReverseField i)
    (SourceBasicReverseExtensionField i) Q _ y hy
    (sourceBasicRationalSubfield_sourceStepRhs_order_dichotomy x hx)
  rwa [adjoin_simple_gen_eq_top] at h
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
