-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_riemannRochProductDifferential_apply_eq_zero_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:31:35.122272+00:00
-- url     : https://prove2.me/submissions/b1b9ce19-5623-4e6d-b558-20609e906ba9

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ResidueProduct
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_riemannRochProductDifferential_mem_localDifferentialLattice_of_ne
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidue_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (omega : Differential k F) (homega : omega ≠ 0)
    (G : Divisor (GlobalPlace k F)) (P Q : GlobalPlace k F) (hQP : Q ≠ P)
    (x : GlobalPlace.riemannRochSubmodule (G + P.placeDivisor))
    (y : GlobalPlace.riemannRochSubmodule
      (differentialDivisor (k := k) (F := F) omega homega - G)) :
    globalSimplePoleResidue (k := k) (F := F)
        (riemannRochProductDifferential omega homega G P x y)
        (riemannRochProductDifferential_isGlobalSimplePole
          omega homega G P x y) Q = 0 := by
  rw [globalSimplePoleResidue_apply]
  change simplePoleTraceResidue (k := k) (F := F) Q
      (riemannRochProductDifferential omega homega G P x y)
      ((riemannRochProductDifferential_isGlobalSimplePole
        omega homega G P x y) Q) = 0
  exact simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
    (k := k) (F := F) Q
    (riemannRochProductDifferential omega homega G P x y)
    ((riemannRochProductDifferential_isGlobalSimplePole
      omega homega G P x y) Q)
    (riemannRochProductDifferential_mem_localDifferentialLattice_of_ne
      omega homega G P Q hQP x y)
end QEC.Coding.AlgebraicGeometry.Differential
