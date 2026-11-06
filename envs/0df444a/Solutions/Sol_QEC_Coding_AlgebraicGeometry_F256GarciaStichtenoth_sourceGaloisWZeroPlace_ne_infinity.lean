-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroPlace_ne_infinity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:34:24.618245+00:00
-- url     : https://prove2.me/submissions/57732aca-262b-437d-ae88-44f64cc754e8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWIntermediate
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ZeroPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroPlace_order_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityPlace_order_generator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open IntermediateField Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution :
    sourceGaloisWZeroPlace ≠ sourceGaloisWInfinityPlace := by
  intro hplaces
  have horder := congrArg
    (fun P : GlobalPlace F256 SourceGaloisWField =>
      P.order sourceGaloisWFieldGenerator) hplaces
  change sourceGaloisWZeroPlace.order sourceGaloisWFieldGenerator =
    sourceGaloisWInfinityPlace.order sourceGaloisWFieldGenerator at horder
  rw [sourceGaloisWZeroPlace_order_generator,
    sourceGaloisWInfinityPlace_order_generator] at horder
  norm_num at horder
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
