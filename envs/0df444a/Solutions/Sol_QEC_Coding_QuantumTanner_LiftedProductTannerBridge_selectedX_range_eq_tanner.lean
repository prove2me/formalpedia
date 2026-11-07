-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LiftedProductTannerBridge.selectedX_range_eq_tanner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:27:06.105666+00:00
-- url     : https://prove2.me/submissions/bd107a1d-c489-4e4c-85a1-f1abe2a1d89b

import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTensorBridge
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTannerBridge
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_selectedXWord_coeff
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_parameterSections_surjective

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
theorem _root_.solution (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (gA : Matrix C' A (ZMod 2)) (a : A → G) (b : B → G) :
    Set.range (selectedXWord hA hB gA a b) =
      (LinearMap.range (tannerXMap a b (tensorCode (matrixRowCode gA) (matrixRowCode hB)))).carrier := by
  ext x
  constructor
  · rintro ⟨V, rfl⟩
    refine ⟨(parameterSections gA hB V.1, parameterSections gA hB V.2), ?_⟩
    ext ⟨i, j, g⟩
    exact (selectedXWord_coeff hA hB gA a b V i j g).symm
  · rintro ⟨T, rfl⟩
    obtain ⟨V0, hV0⟩ := parameterSections_surjective gA hB T.1
    obtain ⟨V1, hV1⟩ := parameterSections_surjective gA hB T.2
    refine ⟨(V0, V1), ?_⟩
    ext ⟨i, j, g⟩
    rw [selectedXWord_coeff, hV0, hV1]
    rfl
end QEC.Coding.QuantumTanner.LiftedProductTannerBridge
