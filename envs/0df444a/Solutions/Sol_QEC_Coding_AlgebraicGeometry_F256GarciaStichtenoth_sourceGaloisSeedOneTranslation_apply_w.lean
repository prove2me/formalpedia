-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSeedOneTranslation_apply_w
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:15:57.462918+00:00
-- url     : https://prove2.me/submissions/dfcbf979-bb40-4321-8aa6-b19a9661e89c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSeedTranslation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSeedOneTranslation_apply_galoisBaseW

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
    sourceGaloisSeedOneTranslation m
        (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) =
      (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) := by
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
      (algebraMap (RatFunc F256) (SourceGaloisClosureField m) galoisBaseW) =
    algebraMap (RatFunc F256) (SourceGaloisClosureField m) galoisBaseW
  rw [AlgEquiv.liftNormal_commutes,
    sourceSeedOneTranslation_apply_galoisBaseW]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
