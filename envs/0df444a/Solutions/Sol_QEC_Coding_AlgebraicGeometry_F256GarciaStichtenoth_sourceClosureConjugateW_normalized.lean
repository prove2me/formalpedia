-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureConjugateW_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:55:51.2162+00:00
-- url     : https://prove2.me/submissions/b939102c-1250-4304-8858-efcd0e2d417e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_EmbeddedWSeed
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWNormal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureConjugateChains
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureConjugateW_adjoin
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_congr_base
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_embeddedSourceW_normalized


set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceConstantBaseTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wConstantBaseTower
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureField m)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m)) :
    PlaceNormalizedExtension Q (sourceClosureWBase m) (f.restrictScalars F256).fieldRange := by
  let E := SourceGaloisClosureField m
  letI : Algebra (SourceField m) E := f.toRingHom.toAlgebra
  letI : IsScalarTower GaloisBaseField (SourceField m) E :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  letI : IsScalarTower F256 (SourceField m) E :=
    IsScalarTower.of_algebraMap_eq' (f.restrictScalars F256).comp_algebraMap.symm
  letI : FiniteDimensional (SourceField m) E :=
    Module.Finite.of_restrictScalars_finite GaloisBaseField (SourceField m) E
  letI : Algebra.IsSeparable (SourceField m) E :=
    Algebra.isSeparable_tower_top_of_isSeparable GaloisBaseField (SourceField m) E
  letI : Algebra (Polynomial F256) E :=
    ((algebraMap (RatFunc F256) E).comp (algebraMap (Polynomial F256) (RatFunc F256))).toAlgebra
  letI : IsScalarTower (Polynomial F256) (RatFunc F256) E := IsScalarTower.of_algebraMap_eq' rfl
  letI : Finite Q.residueField := GlobalPlace.finite_residueField Q
  have h := embeddedSourceW_normalized m Q
  have hbase := sourceClosureConjugateW_adjoin m f
  change F256⟮algebraMap (SourceField m) E
    (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯ = sourceClosureWBase m at hbase
  exact PlaceNormalizedExtension.congr_base Q hbase h
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
