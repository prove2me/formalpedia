-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.uniformizerLogDifferentialClass_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:29:26.610768+00:00
-- url     : https://prove2.me/submissions/89a25c09-7e73-4b59-b85e-f7e429bb636d

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalLogarithmicDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialCoordinate_differential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution (P : GlobalPlace k F) :
    uniformizerLogDifferentialClass (k := k) (F := F) P ≠ 0 := by
  let pi : P.valuationRing := P.uniformizerInValuationRing
  let a : F := functionFieldDerivation (k := k) (F := F) (pi : F)
  have hpi_ne : (pi : F) ≠ 0 := by
    change P.uniformizer ≠ 0
    apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  have ha := uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
    (k := k) (F := F) P
  intro hzero
  change (Submodule.Quotient.mk
      (uniformizerLogDifferential (k := k) (F := F) P) :
        localResidueLine P) = 0 at hzero
  have hquotient :
      (Submodule.Quotient.mk
          (uniformizerLogDifferential (k := k) (F := F) P) :
            localResidueLine P) = 0 := by
    exact hzero
  have hregular := (Submodule.Quotient.mk_eq_zero
    (p := regularDifferentialSubmoduleOfSimplePole P)
    (x := uniformizerLogDifferential (k := k) (F := F) P)).mp hquotient
  change (uniformizerLogDifferential (k := k) (F := F) P : Differential k F) ∈
    localDifferentialLattice P at hregular
  have hcoordinate :=
    (mem_localDifferentialLattice_iff_coordinate_mem_localDerivativeLattice
      (k := k) (F := F) P
      (uniformizerLogDifferential (k := k) (F := F) P : Differential k F)).mp hregular
  have hcoordinate_eq :
      functionFieldDifferentialCoordinate (k := k) (F := F)
          (uniformizerLogDifferential (k := k) (F := F) P : Differential k F) =
        (pi : F)⁻¹ * a := by
    change functionFieldDifferentialCoordinate (k := k) (F := F)
        (logarithmicDifferential (k := k) (F := F) (pi : F)) =
      (pi : F)⁻¹ * a
    rw [logarithmicDifferential, map_smul,
      functionFieldDifferentialCoordinate_differential]
    rfl
  rw [hcoordinate_eq] at hcoordinate
  rcases (ha.2.2 ((pi : F)⁻¹ * a)).mp hcoordinate with hzero' | horder
  · exact (mul_ne_zero (inv_ne_zero hpi_ne) ha.1) hzero'
  · have horder_eq : P.order ((pi : F)⁻¹ * a) = -1 + P.order a := by
      rw [GlobalPlace.order_mul P (inv_ne_zero hpi_ne) ha.1,
        GlobalPlace.order_inv]
      change -P.order P.uniformizer + P.order a = -1 + P.order a
      rw [P.order_uniformizer]
    change P.order a ≤ P.order ((pi : F)⁻¹ * a) at horder
    rw [horder_eq] at horder
    omega
end QEC.Coding.AlgebraicGeometry.Differential
