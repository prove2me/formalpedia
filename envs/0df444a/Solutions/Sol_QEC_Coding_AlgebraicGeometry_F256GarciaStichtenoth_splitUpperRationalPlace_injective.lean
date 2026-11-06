-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:03:13.58779+00:00
-- url     : https://prove2.me/submissions/60f0f21a-e10d-48ed-86d4-8330c9533693

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplittingIdeals
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalSplitting
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitAbovePlace_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Function.Injective (splitUpperRationalPlace Q P x hx hregular) := by
  intro c d hcd
  apply splitAbovePlace_injective Q P x hx hregular
  exact congrArg RationalPlace.place hcd
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
