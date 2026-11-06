-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.principalOrder_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:45:42.843631+00:00
-- url     : https://prove2.me/submissions/a483334e-4b5a-4ac5-b356-14b63f91a009

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_PrincipalOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution (f : Fˣ) :
    principalOrder (k := k) (F := F) f⁻¹ = -principalOrder (k := k) (F := F) f := by
  funext P
  simpa [principalOrder] using order_inv P (f : F)
end QEC.Coding.AlgebraicGeometry.GlobalPlace
