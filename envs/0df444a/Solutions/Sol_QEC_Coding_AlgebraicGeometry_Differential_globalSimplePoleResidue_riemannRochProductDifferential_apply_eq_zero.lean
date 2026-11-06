-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_riemannRochProductDifferential_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:46:16.235772+00:00
-- url     : https://prove2.me/submissions/049735f0-7f5d-40bc-9a25-c52b8cb9f935

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_FunctionFieldGlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ResidueSupportSum
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ResiduePairing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_eq_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_riemannRochProductDifferential_eq_selected


set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential._p2m_local_instance_93312dda23_36
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential._p2m_local_instance_93312dda23_38
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (omega : Differential k F) (homega : omega ≠ 0)
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (x : GlobalPlace.riemannRochSubmodule (G + P.placeDivisor))
    (y : GlobalPlace.riemannRochSubmodule
      (differentialDivisor (k := k) (F := F) omega homega - G)) :
    globalSimplePoleResidue (k := k) (F := F)
        (riemannRochProductDifferential omega homega G P x y)
        (riemannRochProductDifferential_isGlobalSimplePole
          omega homega G P x y) P = 0 := by
  exact
    (globalSimplePoleResidueSum_riemannRochProductDifferential_eq_selected
      omega homega G P x y).symm.trans
      (globalSimplePoleResidueSum_eq_zero (k := k) (F := F)
        (riemannRochProductDifferential omega homega G P x y)
        (riemannRochProductDifferential_isGlobalSimplePole
          omega homega G P x y))
end QEC.Coding.AlgebraicGeometry.Differential
