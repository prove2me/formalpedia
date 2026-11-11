-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.zCorrection_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:26:47.603845+00:00
-- url     : https://prove2.me/submissions/1cd49556-e684-4040-9cef-c3fb9060c440

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualHistory_syndrome
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dual_coboundary1_xSyndrome
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZMap1CoordinateBridge MultiscaleDecoder
open PauliSymplectic BDL26CSSHamiltonian
open scoped Classical BigOperators
namespace QEC.Coding.BDL26TransposedStoppedDecoder
theorem _root_.solution (S : OddScale) (n : Nat) (v : ZSyndromeDomain S n) :
    xSyndrome S (n + 2) (zCorrection S n v) = v.val := by
  unfold zCorrection
  have h := dualHistory_syndrome S n
    (⟨v.val,by
      change v.val ∈ LinearMap.range
        ((dualFamily S (n + 2)).coboundary1 (TopIndex (n + 2)))
      obtain ⟨w,hw⟩ := v.property
      exact ⟨w,((LinearMap.congr_fun
        (dualFamily_coboundary1 S (n + 2) (TopIndex (n + 2))) w).trans
        (LinearMap.congr_fun (dual_coboundary1_xSyndrome S (n + 2)) w)).trans hw⟩⟩)
  exact ((LinearMap.congr_fun
    (dualFamily_coboundary1 S (n + 2) (TopIndex (n + 2))) _).trans
    (LinearMap.congr_fun (dual_coboundary1_xSyndrome S (n + 2)) _)).symm.trans h
end QEC.Coding.BDL26TransposedStoppedDecoder
