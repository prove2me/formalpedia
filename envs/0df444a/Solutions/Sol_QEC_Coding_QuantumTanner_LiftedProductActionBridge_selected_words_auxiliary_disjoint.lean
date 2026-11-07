-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LiftedProductActionBridge.selected_words_auxiliary_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:33:58.231006+00:00
-- url     : https://prove2.me/submissions/73fc386f-d168-4b62-b458-105daccd27b8

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductRestriction
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductActionBridge
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductActionBridge_zWord_auxiliary_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductActionBridge_xWord_auxiliary_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductRestriction_selected_groupAlgebra_auxiliary_disjoint


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductActionBridge
open QEC.Coding.LiftedProduct
open QEC.Coding.QuantumTanner.LiftedProductRestriction
noncomputable section
variable {G A B C D : Type*} [Group G] [Fintype G] [DecidableEq G]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
variable {C' D' : Type*} [Fintype C'] [Fintype D']
namespace QEC.Coding.QuantumTanner.LiftedProductActionBridge
theorem _root_.solution
    (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gA : Matrix C' A (ZMod 2)) (gB : Matrix D' B (ZMod 2))
    (a : A → G) (b : B → G)
    (hDualA : gA * hA.transpose = 0) (hDualB : gB * hB.transpose = 0)
    (U0 U1 : Matrix C D' (MonoidAlgebra (ZMod 2) G))
    (V0 V1 : Matrix C' D (MonoidAlgebra (ZMod 2) G))
    (c : Bool × C) (d : Bool × D) (g : G) :
    zWord hA hB a b
        (zParameter (U0 * twistedMatrix gB (fun j => (b j)⁻¹)) (U1 * scalarMatrix gB))
        (auxiliaryCoordinate c d g) = 0 ∨
      xWord hA hB a b
        (xParameter ((scalarMatrix gA).transpose * V0)
          ((twistedMatrix gA (fun i => (a i)⁻¹)).transpose * V1))
        (auxiliaryCoordinate c d g) = 0 := by
  rw [zWord_auxiliary_eq, xWord_auxiliary_eq]
  rcases selected_groupAlgebra_auxiliary_disjoint hA hB gA gB a b hDualA hDualB
      U0 U1 V0 V1 c d with hz | hx
  · exact Or.inl (congrArg (fun x : MonoidAlgebra (ZMod 2) G => x.coeff g) hz)
  · exact Or.inr (congrArg (fun x : MonoidAlgebra (ZMod 2) G => x.coeff g) hx)
end QEC.Coding.QuantumTanner.LiftedProductActionBridge
