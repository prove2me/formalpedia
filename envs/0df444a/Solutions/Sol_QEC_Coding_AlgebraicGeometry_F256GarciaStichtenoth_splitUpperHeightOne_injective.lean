-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperHeightOne_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:59:59.261295+00:00
-- url     : https://prove2.me/submissions/7f7dfe5a-780d-4e81-8246-ca8a3dc12805

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplittingIdeals
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalSplitting

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Function.Injective (splitUpperHeightOne Q P x hx) := by
  intro c d hcd
  apply splitUpperPrime_injective Q P x hx hregular
  apply Subtype.ext
  exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hcd
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
