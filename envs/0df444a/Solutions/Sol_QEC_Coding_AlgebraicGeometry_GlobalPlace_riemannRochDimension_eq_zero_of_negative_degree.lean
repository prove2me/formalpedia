-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_eq_zero_of_negative_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:33:54.371609+00:00
-- url     : https://prove2.me/submissions/2313ec08-db87-443c-a41a-a5d746b00b7a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_NegativeDegreeVanishing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_FiniteDimensional
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Dimension
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochSubmodule_eq_bot_of_negative_degree


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (G : Divisor (GlobalPlace k F))
    [FiniteDimensional k (riemannRochSubmodule G)]
    (hdegree : Divisor.degree (residueDegree (k := k) (F := F)) G < 0) :
    riemannRochDimension G = 0 := by
  rw [riemannRochDimension,
    riemannRochSubmodule_eq_bot_of_negative_degree k F G hdegree]
  exact finrank_bot k F
end QEC.Coding.AlgebraicGeometry.GlobalPlace
