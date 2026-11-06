-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.mul_mem_riemannRochSubmodule_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:14:35.143125+00:00
-- url     : https://prove2.me/submissions/3a2ccd1c-097f-471d-b5f2-5c996af2d374

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_ValuationBound
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ValuationBound_mul_mem_space_add


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution {G H : Divisor (GlobalPlace k F)} {f g : F}
    (hf : f ∈ riemannRochSubmodule G) (hg : g ∈ riemannRochSubmodule H) :
    f * g ∈ riemannRochSubmodule (G + H) :=
  ValuationBound.mul_mem_space_add valuationFamily hf hg
end QEC.Coding.AlgebraicGeometry.GlobalPlace
