-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_riemannRochSubmodule_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:12:59.89642+00:00
-- url     : https://prove2.me/submissions/7396191a-e677-40eb-88ef-57f98861cbb8

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
theorem _root_.solution (G : Divisor (GlobalPlace k F)) (f : F) :
    f ∈ riemannRochSubmodule G ↔
      ∀ P, P.valuation f ≤ WithZero.exp (G P) :=
  Iff.rfl
end QEC.Coding.AlgebraicGeometry.GlobalPlace
