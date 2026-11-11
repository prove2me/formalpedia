-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.pairedResidual_inGeneratedGroupUpToSign_of_boundaries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:20:41.760194+00:00
-- url     : https://prove2.me/submissions/5592569b-8786-4175-9361-d1d416bcf51c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Theorems.Thm_QEC_Coding_PauliSymplectic_inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZMap1CoordinateBridge MultiscaleDecoder
open PauliSymplectic BDL26CSSHamiltonian
open scoped Classical BigOperators
namespace QEC.Coding.BDL26TransposedStoppedDecoder
theorem _root_.solution (S : OddScale) (n : Nat)
    (u : XSyndromeDomain S n) (v : ZSyndromeDomain S n) (E : Binary (Physical S (n + 2)))
    (hx : ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (pairedResidual S n u v E).vector.xPart)
    (hz : ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (pairedResidual S n u v E).vector.zPart) :
    (binaryCSSStabilizerCodeOfParityChecks (zSyndrome S (n + 2)) (xSyndrome S (n + 2))
      (row_orthogonal S (n + 2))).InGeneratedGroupUpToSign (pairedResidual S n u v E) := by
  apply (inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff _ _ _ _).mpr
  exact ⟨hx,hz⟩
end QEC.Coding.BDL26TransposedStoppedDecoder
