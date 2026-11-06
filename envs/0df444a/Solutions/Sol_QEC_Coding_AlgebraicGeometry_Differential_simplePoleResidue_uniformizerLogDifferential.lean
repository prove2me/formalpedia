-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_uniformizerLogDifferential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:33:53.431309+00:00
-- url     : https://prove2.me/submissions/c72d21d7-60e6-40b2-b575-eca8910d3020

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidueEquiv_uniformizerLogDifferentialClass

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
    simplePoleResidue (k := k) (F := F) P
        (uniformizerLogDifferential (k := k) (F := F) P) = 1 := by
  exact simplePoleResidueEquiv_uniformizerLogDifferentialClass
        (k := k) (F := F) P
end QEC.Coding.AlgebraicGeometry.Differential
