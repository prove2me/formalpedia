-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitAbovePlace_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:36:01.60297+00:00
-- url     : https://prove2.me/submissions/1f0eb0c5-a3cf-45a2-b6f7-8f813fdc21e8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplittingIdeals
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRationalSplitting
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperHeightOne_injective

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
    Function.Injective (sourceSplitAbovePlace Q P x hx) := by
  intro c d hcd
  apply sourceSplitUpperHeightOne_injective Q P x hx hregular hsplit
  apply IsDedekindDomain.HeightOneSpectrum.ext
  ext y
  let C := sourceSplitUpperHeightOne Q P x hx c
  let D := sourceSplitUpperHeightOne Q P x hx d
  have hvaluation : C.valuation (SourceStepField P x hx) =
      D.valuation (SourceStepField P x hx) :=
    congrArg GlobalPlace.valuation hcd
  change y ∈ C.asIdeal ↔ y ∈ D.asIdeal
  rw [← C.valuation_lt_one_iff_mem (K := SourceStepField P x hx),
    hvaluation, D.valuation_lt_one_iff_mem]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
