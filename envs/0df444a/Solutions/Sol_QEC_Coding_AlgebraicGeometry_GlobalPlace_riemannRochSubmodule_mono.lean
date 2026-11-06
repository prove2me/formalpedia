-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:14:28.515488+00:00
-- url     : https://prove2.me/submissions/3f788a7f-fa4b-4556-ac2f-f6707ec48571

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_ValuationBound
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ValuationBound_space_mono


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution {G H : Divisor (GlobalPlace k F)}
    (hGH : G ≤ H) : riemannRochSubmodule G ≤ riemannRochSubmodule H :=
  ValuationBound.space_mono valuationFamily hGH
end QEC.Coding.AlgebraicGeometry.GlobalPlace
