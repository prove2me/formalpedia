-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSeedOneTranslation_apply_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:17:13.718275+00:00
-- url     : https://prove2.me/submissions/e8a8ab34-8b65-49c6-95a2-935d87ebeba3

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSeedTranslation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSeedOneTranslation_apply_X

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open IntermediateField Polynomial
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSeedTranslation_f256CharTwo
attribute [local instance] sourceGaloisSeedTranslation_f256CharTwo
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSeedTranslation_ratFuncCharTwo
attribute [local instance] sourceGaloisSeedTranslation_ratFuncCharTwo
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    sourceGaloisSeedOneTranslation m (sourceGaloisSeedCoordinate m) =
      sourceGaloisSeedCoordinate m + 1 := by
  let seedAlgebra : Algebra (RatFunc F256) (SourceGaloisClosureField m) :=
    (sourceGaloisSeedRatFuncToClosure m).toRingHom.toAlgebra
  letI seedSMul : SMul (RatFunc F256) (SourceGaloisClosureField m) :=
    seedAlgebra.toSMul
  letI seedAlgebraInstance : Algebra (RatFunc F256)
      (SourceGaloisClosureField m) := seedAlgebra
  letI seedModule : Module (RatFunc F256) (SourceGaloisClosureField m) :=
    @Algebra.toModule (RatFunc F256) (SourceGaloisClosureField m) _ _
      seedAlgebraInstance
  letI seedTower : IsScalarTower GaloisBaseField (RatFunc F256)
      (SourceGaloisClosureField m) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro a
      change algebraMap GaloisBaseField (SourceGaloisClosureField m) a =
        sourceGaloisSeedRatFuncToClosure m
          (algebraMap GaloisBaseField (RatFunc F256) a)
      exact (sourceGaloisSeedRatFuncToClosure m).commutes a |>.symm)
  change sourceSeedOneTranslation.liftNormal (SourceGaloisClosureField m)
      (algebraMap (RatFunc F256) (SourceGaloisClosureField m) RatFunc.X) =
    algebraMap (RatFunc F256) (SourceGaloisClosureField m) RatFunc.X + 1
  rw [AlgEquiv.liftNormal_commutes, sourceSeedOneTranslation_apply_X,
    map_add, map_one]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
