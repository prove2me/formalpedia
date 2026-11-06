-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.leftMarginal_toOperator_eq_partialTraceLeftRaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:52:56.514636+00:00
-- url     : https://prove2.me/submissions/51636775-dd73-4cf6-8692-9fd0416f8e7e

import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity

set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.DensityOperator
namespace QEC.Semantics.DensityOperator
theorem _root_.solution
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] (rho : DensityOperator (CompositeSystem H K)) :
    (leftMarginal rho).toOperator = FiniteMatrixEntropy.partialTraceLeftRaw H K rho.toOperator := by
  rfl
end QEC.Semantics.DensityOperator
