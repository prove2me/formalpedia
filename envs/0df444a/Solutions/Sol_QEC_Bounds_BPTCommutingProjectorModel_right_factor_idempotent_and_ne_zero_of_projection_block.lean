-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.right_factor_idempotent_and_ne_zero_of_projection_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:06:10.882048+00:00
-- url     : https://prove2.me/submissions/182226bb-87ef-4c07-bfac-de5afdf96d3e

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ScalarTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_TensorFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_right_factor_ne_zero_of_nonzero_unitary_tensor_block
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_congr
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_conjOperator_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_right_factor_idempotent_of_tensor_product_projection


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
    {S H K : Type u} [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S] [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (T : Semantics.UnitaryTransport S (Semantics.CompositeSystem H K))
    (R : Semantics.Operator S) (P : Semantics.Operator H) (Q : Semantics.Operator K)
    (hR : R ≠ 0) (hP : P.IsSymmetricProjection) (hP0 : P ≠ 0)
    (hRprojection : R.IsSymmetricProjection)
    (hblock : T.conjOperator R = TensorProduct.map P Q) :
    Q * Q = Q ∧ Q ≠ 0 := by
  have hblockProjection : (TensorProduct.map P Q).IsSymmetricProjection :=
    isSymmetricProjection_congr
      ((isSymmetricProjection_conjOperator_iff T R).mpr hRprojection) hblock
  exact ⟨right_factor_idempotent_of_tensor_product_projection P Q
      hP.isIdempotentElem hP0 hblockProjection,
    right_factor_ne_zero_of_nonzero_unitary_tensor_block T R P Q hR hblock⟩
end QEC.Bounds.BPTCommutingProjectorModel
