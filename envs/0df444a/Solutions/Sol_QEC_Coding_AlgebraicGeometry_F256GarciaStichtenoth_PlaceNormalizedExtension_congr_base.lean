-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.PlaceNormalizedExtension.congr_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:22:26.840073+00:00
-- url     : https://prove2.me/submissions/dd144b52-7663-45eb-b474-5aab4aa12e5f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AmbientPlaceModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementBaseTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceRefinement

set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
namespace PlaceNormalizedExtension
theorem _root_.solution (Q : GlobalPlace F256 E)
    {K K' L : IntermediateField F256 E}
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [FiniteDimensional K' E] [Algebra.IsSeparable K' E]
    (heq : K = K') (h : PlaceNormalizedExtension Q K L) :
    PlaceNormalizedExtension Q K' L := by
  subst K'
  exact h
end PlaceNormalizedExtension
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
