-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_le_rightMarginal_add_card_mul_log_uniformDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:15:00.364592+00:00
-- url     : https://prove2.me/submissions/7022973d-cd51-456b-a61d-09583d9cac02

import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_le_rightMarginal_add_sum_log_selectedDimensions
import Theorems.Thm_QEC_Semantics_QuditSubsystem_sum_log_selectedDimensions_le_card_mul_log_uniformDimension


set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.DensityOperator
namespace QEC.Semantics.DensityOperator
theorem _root_.solution
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {ι : Type u} [Fintype ι] [DecidableEq ι]
    {q : ι -> Nat} (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) (D : Nat)
    (hD : ∀ i, i ∈ S.selected -> q i <= D)
    (rho : DensityOperator (CompositeSystem H S.selectedSystem)) :
    rho.vonNeumannEntropy <= (rightMarginal rho).vonNeumannEntropy +
      (S.selected.card : Real) * Real.logb 2 (D : Real) := by
  exact (vonNeumannEntropy_le_rightMarginal_add_sum_log_selectedDimensions S rho).trans
    (add_le_add_right
      (S.sum_log_selectedDimensions_le_card_mul_log_uniformDimension hq D hD) _)
end QEC.Semantics.DensityOperator
