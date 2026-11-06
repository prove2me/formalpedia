-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_unitMulUniformizerLogDifferential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:28:42.809938+00:00
-- url     : https://prove2.me/submissions/29338e98-49b1-4d74-a96d-57927c71c579

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidueEquiv_uniformizerLogDifferentialClass
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_unitMulUniformizerLogDifferentialClass_eq


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
    (P : GlobalPlace k F) (u : P.valuationRingˣ) :
    simplePoleResidue (k := k) (F := F) P
        (unitMulUniformizerLogDifferential (k := k) (F := F) P u) = 1 := by
  change simplePoleResidueEquiv (k := k) (F := F) P
      (Submodule.Quotient.mk
        (unitMulUniformizerLogDifferential (k := k) (F := F) P u)) = 1
  rw [unitMulUniformizerLogDifferentialClass_eq (k := k) (F := F) P u]
  exact simplePoleResidueEquiv_uniformizerLogDifferentialClass
    (k := k) (F := F) P
end QEC.Coding.AlgebraicGeometry.Differential
