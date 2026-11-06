-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepLiteral_adjoin_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:05:40.22621+00:00
-- url     : https://prove2.me/submissions/af93b27a-3d1a-4403-97a9-74a3f7e62c9c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_LiteralSourceStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStep_finrank


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
    Module.finrank K K⟮y⟯ = 16 := by
  rw [← (sourceStepLiteralAdjoinEquiv P x hx y hy).toLinearEquiv.finrank_eq]
  exact sourceStep_finrank P x hx
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
