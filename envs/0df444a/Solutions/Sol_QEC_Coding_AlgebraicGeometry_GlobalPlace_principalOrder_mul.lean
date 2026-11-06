-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.principalOrder_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:45:38.757616+00:00
-- url     : https://prove2.me/submissions/372cca3b-a243-4a05-8120-ba276febc209

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_PrincipalOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution (f g : Fˣ) :
    principalOrder (k := k) (F := F) (f * g) =
      principalOrder (k := k) (F := F) f + principalOrder (k := k) (F := F) g := by
  funext P
  simpa [principalOrder] using
    order_mul P (f := (f : F)) (g := (g : F)) f.ne_zero g.ne_zero
end QEC.Coding.AlgebraicGeometry.GlobalPlace
