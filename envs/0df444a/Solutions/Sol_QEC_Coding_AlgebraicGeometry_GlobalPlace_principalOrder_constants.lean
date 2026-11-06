-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.principalOrder_constants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:45:48.009204+00:00
-- url     : https://prove2.me/submissions/a1bd63a2-08bd-4138-a95d-46e9e07ab364

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_PrincipalOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_algebraMap


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution (a : kˣ) :
    principalOrder (k := k) (F := F) (Units.map (algebraMap k F) a : Fˣ) = 0 := by
  funext P
  simpa [principalOrder] using order_algebraMap P (a : k) a.ne_zero
end QEC.Coding.AlgebraicGeometry.GlobalPlace
