-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferential_eq_residueCoordinate_smul_uniformizerLogDifferential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:35:10.303072+00:00
-- url     : https://prove2.me/submissions/b5b89efe-5771-4c18-b181-65c8aad69c79

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_simplePoleResidueCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDerivation_uniformizer_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialCoordinate_differential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer

section
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
namespace Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
private theorem coordinate_uniformizerLogDifferential (P : GlobalPlace k F) :
    functionFieldDifferentialCoordinate (k := k) (F := F)
        (uniformizerLogDifferential (k := k) (F := F) P : Differential k F) =
      (P.uniformizerInValuationRing : F)⁻¹ *
        functionFieldDerivation (k := k) (F := F)
          (P.uniformizerInValuationRing : F) := by
  change functionFieldDifferentialCoordinate (k := k) (F := F)
      (logarithmicDifferential (k := k) (F := F)
        (P.uniformizerInValuationRing : F)) = _
  rw [logarithmicDifferential, map_smul,
    functionFieldDifferentialCoordinate_differential]
  rfl
end Differential
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (P : GlobalPlace k F) (omega : simplePoleDifferentialLattice P) :
    (omega : Differential k F) =
      simplePoleResidueCoordinate (k := k) (F := F) P omega •
        (uniformizerLogDifferential (k := k) (F := F) P : Differential k F) := by
  let pi : P.valuationRing := P.uniformizerInValuationRing
  let a : F := functionFieldDerivation (k := k) (F := F) (pi : F)
  let C : Differential k F →ₗ[F] F :=
    functionFieldDifferentialCoordinate (k := k) (F := F)
  have hpi_ne : (pi : F) ≠ 0 := by
    change P.uniformizer ≠ 0
    apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  have ha_ne : a ≠ 0 :=
    functionFieldDerivation_uniformizer_ne_zero (k := k) (F := F) P
  apply (functionFieldDifferentialEquiv (k := k) (F := F)).injective
  change C (omega : Differential k F) =
    C (simplePoleResidueCoordinate (k := k) (F := F) P omega •
      (uniformizerLogDifferential (k := k) (F := F) P : Differential k F))
  rw [C.map_smul_of_tower, coordinate_uniformizerLogDifferential]
  change C (omega : Differential k F) =
    ((simplePoleResidueCoordinate (k := k) (F := F) P omega :
      P.valuationRing) : F) * ((pi : F)⁻¹ * a)
  rw [coe_simplePoleResidueCoordinate]
  change C (omega : Differential k F) =
    ((pi : F) * C (omega : Differential k F) * a⁻¹) * ((pi : F)⁻¹ * a)
  field_simp [hpi_ne, ha_ne]
end QEC.Coding.AlgebraicGeometry.Differential
