-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LiftedProductTannerBridge.parameterSections_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:23:53.284049+00:00
-- url     : https://prove2.me/submissions/12afcf65-537c-49a2-b9d7-a0ddb2ea5ac9

import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTensorBridge
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTannerBridge
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTensorBridge_mem_tensorCode_iff_tensorMatrix


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductTannerBridge
open Classical
open LiftedProductRestriction LiftedProductActionBridge LiftedProductTensorBridge
universe v
variable {G A B C D C' D' : Type v} [Group G] [Fintype G] [DecidableEq G]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
  [Fintype C'] [DecidableEq C'] [Fintype D'] [DecidableEq D']
namespace QEC.Coding.QuantumTanner.LiftedProductTannerBridge
theorem _root_.solution (P : Matrix C A (ZMod 2)) (Q : Matrix D B (ZMod 2)) :
    Function.Surjective (parameterSections (G := G) P Q) := by
  intro T
  have h : ∀ u : G, ∃ U : Matrix C D (ZMod 2), tensorMatrix P Q U = (T u).val :=
    fun u => (mem_tensorCode_iff_tensorMatrix P Q (T u).val).1 (T u).property
  choose U hU using h
  let packed : Matrix C D (MonoidAlgebra (ZMod 2) G) :=
    fun c d => MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm (fun u => U u c d))
  refine ⟨packed, ?_⟩
  funext u
  apply Subtype.ext
  change tensorMatrix P Q (fun c d => (packed c d).coeff u) = (T u).val
  rw [← hU u]
  congr 1
end QEC.Coding.QuantumTanner.LiftedProductTannerBridge
