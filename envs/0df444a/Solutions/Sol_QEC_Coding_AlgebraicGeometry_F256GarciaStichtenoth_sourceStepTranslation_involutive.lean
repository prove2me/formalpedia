-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepTranslation_involutive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:34:56.573556+00:00
-- url     : https://prove2.me/submissions/3944fe10-6ac5-4da0-b9b1-364e10d92910

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
import Mathlib.FieldTheory.Galois.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisStep

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier)
    (y : SourceStepField P x hx) :
    sourceStepTranslation P x hx c (sourceStepTranslation P x hx c y) = y := by
  have hcomp := congrArg
    (fun f : SourceStepField P x hx →ₐ[K] SourceStepField P x hx => f y)
    (sourceStepTranslationHom_comp_self P x hx c)
  exact hcomp
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
