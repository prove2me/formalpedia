-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule_eq_bot_of_negative_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:32:47.106566+00:00
-- url     : https://prove2.me/submissions/7dba4fcf-d6eb-4192-8aa5-a1906161c2b2

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_NegativeDegreeVanishing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_divisorDegree_nonnegative_of_mem_nonzero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
variable [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
theorem _root_.solution
    (G : Divisor (GlobalPlace k F))
    (hdegree : Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G < 0) :
    GlobalPlace.riemannRochSubmodule G = ⊥ := by
  apply le_antisymm
  · intro f hmem
    change f = 0
    by_contra hf
    have hnonnegative :=
      GlobalPlace.divisorDegree_nonnegative_of_mem_nonzero k F G hmem hf
    exact (not_lt_of_ge hnonnegative) hdegree
  · exact bot_le
end GlobalPlace
end QEC.Coding.AlgebraicGeometry
