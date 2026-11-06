-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicForward_normalizedRefinement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:32:28.078516+00:00
-- url     : https://prove2.me/submissions/ca0e5298-db88-4649-9764-2e8cda9717d8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionFields
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_adjoin_simple_gen_eq_top
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_artinSchreier16_bottom_normalizedRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicForwardEmbedded_rhs_order_dichotomy


set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (i : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (SourceBasicForwardField i)] [IsFractionRing A (SourceBasicForwardField i)]
    [Algebra A (SourceBasicForwardExtensionField i)]
    [IsScalarTower A (SourceBasicForwardField i) (SourceBasicForwardExtensionField i)]
    [Module.Finite A (integralClosure A (SourceBasicForwardExtensionField i))]
    (Q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure A (SourceBasicForwardExtensionField i))) :
    NormalizedRefinement A (SourceBasicForwardField i) (SourceBasicForwardExtensionField i)
      Q ⊥ ⊤ := by
  let y := AdjoinSimple.gen (SourceBasicForwardField i) (sourceDistinguishedCoordinate (i + 1))
  have hy : y ^ 16 + y = algebraMap (SourceBasicForwardField i)
      (SourceBasicForwardExtensionField i)
      (sourceStepRhs (AdjoinSimple.gen F256
        (sourceRecursionEmbedding i (sourceDistinguishedCoordinate i)))) := by
    apply Subtype.ext
    exact sourceBasicForward_root_equation i
  have h := artinSchreier16_bottom_normalizedRefinement A (SourceBasicForwardField i)
    (SourceBasicForwardExtensionField i) Q _ y hy
    (sourceBasicForwardEmbedded_rhs_order_dichotomy i)
  rwa [adjoin_simple_gen_eq_top] at h
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
