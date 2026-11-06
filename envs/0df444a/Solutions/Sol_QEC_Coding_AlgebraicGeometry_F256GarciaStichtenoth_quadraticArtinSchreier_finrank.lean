-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreier_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:48:10.16649+00:00
-- url     : https://prove2.me/submissions/a7c070fb-fef6-4dd9-b0a1-6f7d0ffbc837

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Module.finrank K (QuadraticArtinSchreierField P a ha) = 2 := by
  calc
    Module.finrank K (QuadraticArtinSchreierField P a ha) =
        (AdjoinRoot.powerBasis
          (quadraticArtinSchreierPolynomial_monic P a ha).ne_zero).dim :=
      PowerBasis.finrank _
    _ = (quadraticArtinSchreierPolynomial P a ha).natDegree := rfl
    _ = 2 := quadraticArtinSchreierPolynomial_natDegree P a ha
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
