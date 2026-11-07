-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LiftedProductTannerBridge.selectedZ_range_eq_tanner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:27:04.540342+00:00
-- url     : https://prove2.me/submissions/da6d718a-cf35-4d0d-959c-f13a38490f67

import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTensorBridge
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTannerBridge
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_selectedZWord_coeff
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
    (hB : Matrix D B (ZMod 2)) (gB : Matrix D' B (ZMod 2)) (a : A → G) (b : B → G) :
    Set.range (selectedZWord hA hB gB a b) =
      (LinearMap.range (tannerZMap a b (tensorCode (matrixRowCode hA) (matrixRowCode gB)))).carrier := by
  ext x
  constructor
  · rintro ⟨U, rfl⟩
    refine ⟨(parameterSections hA gB U.1, parameterSections hA gB U.2), ?_⟩
    ext ⟨i, j, g⟩
    exact (selectedZWord_coeff hA hB gB a b U i j g).symm
  · rintro ⟨T, rfl⟩
    obtain ⟨U0, hU0⟩ := parameterSections_surjective hA gB T.1
    obtain ⟨U1, hU1⟩ := parameterSections_surjective hA gB T.2
    refine ⟨(U0, U1), ?_⟩
    ext ⟨i, j, g⟩
    rw [selectedZWord_coeff, hU0, hU1]
    rfl
end QEC.Coding.QuantumTanner.LiftedProductTannerBridge
