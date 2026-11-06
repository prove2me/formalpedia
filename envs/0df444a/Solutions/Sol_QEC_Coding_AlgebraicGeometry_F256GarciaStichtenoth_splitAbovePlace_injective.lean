-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitAbovePlace_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:01:06.931332+00:00
-- url     : https://prove2.me/submissions/4ef00d44-6f4b-4147-8034-e6c17118ac10

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplittingIdeals
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalSplitting
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperHeightOne_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Function.Injective (splitAbovePlace Q P x hx) := by
  intro c d hcd
  apply splitUpperHeightOne_injective Q P x hx hregular
  apply IsDedekindDomain.HeightOneSpectrum.ext
  ext y
  let C := splitUpperHeightOne Q P x hx c
  let D := splitUpperHeightOne Q P x hx d
  have hvaluation : C.valuation (StepField P x hx) =
      D.valuation (StepField P x hx) :=
    congrArg GlobalPlace.valuation hcd
  change y ∈ C.asIdeal ↔ y ∈ D.asIdeal
  rw [← C.valuation_lt_one_iff_mem (K := StepField P x hx),
    hvaluation, D.valuation_lt_one_iff_mem]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
