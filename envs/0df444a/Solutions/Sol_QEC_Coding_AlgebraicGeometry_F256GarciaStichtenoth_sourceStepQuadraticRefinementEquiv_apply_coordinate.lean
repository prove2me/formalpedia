-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepQuadraticRefinementEquiv_apply_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:04:47.090195+00:00
-- url     : https://prove2.me/submissions/c66ab3e0-2f78-4e11-bd9c-eb9a4396a358

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
universe u
variable {K : Type u} [Field K] [Algebra F256 K]
@[simp]
private theorem sourceStepToQuadraticRefinementHom_apply_root
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepToQuadraticRefinementHom P x hx
        (sourceStepReciprocalRoot P x hx) =
      (quadraticArtinSchreierTowerCoordinate P (sourceStepRhs x)
        (sourceStepRhs_order P x hx) 4)⁻¹ := by
  dsimp only [sourceStepToQuadraticRefinementHom, sourceStepReciprocalRoot]
  erw [AdjoinRoot.liftAlgHom_root]
@[simp]
private theorem sourceStepQuadraticRefinementEquiv_apply
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (z : SourceStepField P x hx) :
    sourceStepQuadraticRefinementEquiv P x hx z =
      sourceStepToQuadraticRefinementHom P x hx z := by
  dsimp only [sourceStepQuadraticRefinementEquiv]
  erw [AlgEquiv.ofBijective_apply]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
universe u
variable {K : Type u} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepQuadraticRefinementEquiv P x hx
        (sourceStepCoordinate P x hx) =
      quadraticArtinSchreierTowerCoordinate P (sourceStepRhs x)
        (sourceStepRhs_order P x hx) 4 := by
  rw [sourceStepCoordinate, map_inv₀]
  rw [sourceStepQuadraticRefinementEquiv_apply,
    sourceStepToQuadraticRefinementHom_apply_root, inv_inv]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
