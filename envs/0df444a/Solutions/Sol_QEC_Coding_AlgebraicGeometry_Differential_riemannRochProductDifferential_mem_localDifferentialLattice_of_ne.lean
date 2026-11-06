-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.riemannRochProductDifferential_mem_localDifferentialLattice_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:29:02.101346+00:00
-- url     : https://prove2.me/submissions/ffd2dacc-879a-471e-8973-c4bf90104bfe

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ResidueProduct
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_smul_mem_localDifferentialLattice_iff_order_add_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



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
    riemannRochProductDifferential omega homega G P x y ∈
      localDifferentialLattice Q := by
  by_cases hx : (x : F) = 0
  · simp only [riemannRochProductDifferential, hx, zero_mul, zero_smul]
    exact (localDifferentialLattice Q).zero_mem
  by_cases hy : (y : F) = 0
  · simp only [riemannRochProductDifferential, hy, mul_zero, zero_smul]
    exact (localDifferentialLattice Q).zero_mem
  have hxy : (x : F) * (y : F) ≠ 0 := mul_ne_zero hx hy
  apply (smul_mem_localDifferentialLattice_iff_order_add_nonnegative
    (k := k) (F := F) Q ((x : F) * (y : F)) hxy omega homega).mpr
  rw [GlobalPlace.order_mul Q hx hy]
  have hxQ :=
    (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (G + P.placeDivisor) hx).mp x.property Q
  have hyQ :=
    (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (differentialDivisor (k := k) (F := F) omega homega - G) hy).mp
        y.property Q
  rw [Finsupp.add_apply,
    GlobalPlace.placeDivisor_apply_of_ne P Q (Ne.symm hQP), add_zero] at hxQ
  simp only [Finsupp.sub_apply, differentialDivisor_apply] at hyQ
  omega
end QEC.Coding.AlgebraicGeometry.Differential
