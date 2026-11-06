-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepTranslation_apply_auxiliaryCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:52:15.362444+00:00
-- url     : https://prove2.me/submissions/dbadd8e7-1b47-4091-8e89-d050342c2050

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Translation

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    stepTranslation P x hx c (stepAuxiliaryCoordinate P x hx) =
      stepAuxiliaryCoordinate P x hx +
        algebraMap F256 (StepField P x hx) (c : F256) :=
  stepTranslationHom_apply_auxiliaryCoordinate P x hx c
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
