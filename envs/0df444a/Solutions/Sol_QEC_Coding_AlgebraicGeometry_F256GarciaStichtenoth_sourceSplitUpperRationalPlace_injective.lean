-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:37:34.882792+00:00
-- url     : https://prove2.me/submissions/7cc7ddf0-8e99-43bd-acb1-d0ac57620cdb

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplittingIdeals
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRationalSplitting
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitAbovePlace_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    Function.Injective
      (sourceSplitUpperRationalPlace Q P x hx hregular hsplit) := by
  intro c d hcd
  apply sourceSplitAbovePlace_injective Q P x hx hregular hsplit
  exact congrArg RationalPlace.place hcd
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
