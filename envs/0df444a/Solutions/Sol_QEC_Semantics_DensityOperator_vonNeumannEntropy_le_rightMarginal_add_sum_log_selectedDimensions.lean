-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_le_rightMarginal_add_sum_log_selectedDimensions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:04:09.2502+00:00
-- url     : https://prove2.me/submissions/2337d03c-fd86-4ee5-b076-21b7a12f196b

import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_subadditive_bipartite
import Theorems.Thm_QEC_Semantics_QuditSubsystem_vonNeumannEntropy_le_sum_log_selectedDimensions


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
    {q : ι -> Nat} (S : QuditSubsystem q)
    (rho : DensityOperator (CompositeSystem H S.selectedSystem)) :
    rho.vonNeumannEntropy <= (rightMarginal rho).vonNeumannEntropy +
      ∑ i ∈ S.selected, Real.logb 2 (q i : Real) := by
  exact (vonNeumannEntropy_subadditive_bipartite rho).trans
    (add_le_add_right (S.vonNeumannEntropy_le_sum_log_selectedDimensions (leftMarginal rho)) _)
end QEC.Semantics.DensityOperator
