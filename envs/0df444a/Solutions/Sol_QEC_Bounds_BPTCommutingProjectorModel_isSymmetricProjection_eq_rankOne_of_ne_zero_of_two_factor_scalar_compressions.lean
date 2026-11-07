-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_eq_rankOne_of_ne_zero_of_two_factor_scalar_compressions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:41:35.741452+00:00
-- url     : https://prove2.me/submissions/ff58d195-677b-45bb-9d9a-37a176f68231

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_PartialTrace
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finrank_range_le_one_of_two_factor_scalar_compressions
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_eq_rankOne_of_ne_zero_of_range_finrank_le_one


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem N C))
    (hP : P.IsSymmetricProjection) (hP0 : P ≠ 0)
    (hleft : ∀ X : Semantics.Operator N, ∃ scalar : Complex,
      P * TensorProduct.map X (1 : Semantics.Operator C) * P = scalar • P)
    (hright : ∀ Y : Semantics.Operator C, ∃ scalar : Complex,
      P * TensorProduct.map (1 : Semantics.Operator N) Y * P = scalar • P) :
    ∃ phi : Semantics.CompositeSystem N C, ‖phi‖ = 1 ∧
      P = (InnerProductSpace.rankOne Complex phi phi).toLinearMap := by
  exact isSymmetricProjection_eq_rankOne_of_ne_zero_of_range_finrank_le_one P hP hP0
    (finrank_range_le_one_of_two_factor_scalar_compressions P hP hleft hright)
end QEC.Bounds.BPTCommutingProjectorModel
