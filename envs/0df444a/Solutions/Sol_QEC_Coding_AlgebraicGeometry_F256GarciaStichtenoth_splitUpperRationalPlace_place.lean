-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_place
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:00:39.163543+00:00
-- url     : https://prove2.me/submissions/15c08385-530d-451c-b55c-c366c863ef9d

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
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    (splitUpperRationalPlace Q P x hx hregular c).place =
      splitAbovePlace Q P x hx c :=
  rfl
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
