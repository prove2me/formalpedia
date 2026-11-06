-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.allLocalScalarCompression_union_of_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:09:34.899726+00:00
-- url     : https://prove2.me/submissions/e664fb71-6af7-4634-b74a-c6e2477c22d0

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Support
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorization
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extend_union_rankOne_eq_product
import Theorems.Thm_QEC_Semantics_QuditSubsystem_allLocalScalarCompression_of_rankOne_basis


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
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right)
    (hproduct : ∀ (A : Semantics.Operator (M.regionSubsystem left).selectedSystem)
      (B : Semantics.Operator (M.regionSubsystem right).selectedSystem),
      Semantics.QuditSubsystem.ScalarCompression M.codeSpace
        ((M.regionSubsystem left).extendLocalToRegister A *
          (M.regionSubsystem right).extendLocalToRegister B)) :
    Semantics.QuditSubsystem.AllLocalScalarCompression M.codeSpace
      (M.regionSubsystem (left ∪ right)) := by
  let R := M.regionSubsystem (left ∪ right)
  let basis := EuclideanSpace.basisFun (Semantics.Qudit.Label R.selectedDimensions) Complex
  apply Semantics.QuditSubsystem.allLocalScalarCompression_of_rankOne_basis basis
  intro labels labels'
  rw [M.extend_union_rankOne_eq_product left right hdisjoint labels labels']
  exact hproduct _ _
end QEC.Bounds.BPTCommutingProjectorModel
