-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.xCorrection_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:21:17.058206+00:00
-- url     : https://prove2.me/submissions/a0be4ad4-f63f-4c56-9c1c-ec0972b2c385

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_actualHistory_syndrome
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
theorem _root_.solution (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) :
    zSyndrome S (n + 2) (xCorrection S n u) = u.val := by
  unfold xCorrection
  have h := BDL26OwnerIncidenceMasks.actualHistory_syndrome S n
    (⟨u.val,by
      change u.val ∈ LinearMap.range
        ((indexedFamily S (n + 2)).coboundary1 (TopIndex (n + 2)))
      obtain ⟨w,hw⟩ := u.property
      exact ⟨w,(LinearMap.congr_fun
        (indexedFamily_coboundary1 S (n + 2) (TopIndex (n + 2))) w).trans hw⟩⟩)
  exact (LinearMap.congr_fun
    (indexedFamily_coboundary1 S (n + 2) (TopIndex (n + 2))) _).symm.trans h
end QEC.Coding.BDL26TransposedStoppedDecoder
