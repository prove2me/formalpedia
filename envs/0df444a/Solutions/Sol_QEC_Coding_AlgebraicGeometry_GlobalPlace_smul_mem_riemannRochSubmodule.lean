-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.smul_mem_riemannRochSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:34.68223+00:00
-- url     : https://prove2.me/submissions/8ee3c6de-0acb-4164-b56c-ea81975f66be

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_ValuationBound
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution {G : Divisor (GlobalPlace k F)}
    (a : k) {f : F} (hf : f ∈ riemannRochSubmodule G) :
    a • f ∈ riemannRochSubmodule G :=
  (riemannRochSubmodule G).smul_mem a hf
end QEC.Coding.AlgebraicGeometry.GlobalPlace
