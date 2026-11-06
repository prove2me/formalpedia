-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepLiteralQuadraticRefinementEquiv_apply_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:31:42.804558+00:00
-- url     : https://prove2.me/submissions/2f3c58dc-1957-4556-b856-2167dba32d4e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_LiteralSourceStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepQuadraticRefinementEquiv_apply_coordinate


set_option autoImplicit false
open Polynomial IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K E : Type*} [_root_.Field K] [_root_.Field E]
  [Algebra F256 K] [Algebra K E]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (y : E) (hy : y ^ 16 + y = algebraMap K E (sourceStepRhs x)) :
    sourceStepLiteralQuadraticRefinementEquiv P x hx y hy
        (quadraticArtinSchreierTowerCoordinate P (sourceStepRhs x)
          (sourceStepRhs_order P x hx) 4) = AdjoinSimple.gen K y := by
  rw [sourceStepLiteralQuadraticRefinementEquiv, AlgEquiv.trans_apply,
    ← sourceStepQuadraticRefinementEquiv_apply_coordinate P x hx,
    AlgEquiv.symm_apply_apply]
  exact sourceStepLiteralAdjoinHom_apply_coordinate P x hx y hy
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
