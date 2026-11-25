-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_proof_7648869e9d91
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:23:54.346979+00:00
-- url     : https://prove2.me/submissions/a4b8a9dc-52b0-42f9-aa36-885fa9ef99f0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isGradedSub_bot_2eb73de8a2a9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_exists_chain_cffe35f4d0ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_card_eq_length_of_filtration_eb2ffd839cfb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace MultigradedFiltration
theorem _root_.solution : MultigradedFiltration.Statement.{u, v} := by
  intro F _ K _ _ ι _ M _ _ _ _ _ piece hM
  classical
  letI := hM.internal.chooseDecomposition
  obtain ⟨n, N, x, c, q, h0, hl, hj⟩ :=
    MultigradedFiltration.exists_chain hM ⊥ MultigradedFiltration.isGradedSub_bot
  refine ⟨n, N, x, c, q, h0, hl, hj, fun W hW => ?_⟩
  haveI : W.IsPrime := hW.1.1
  convert GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.card_eq_length_of_filtration N x q h0 hl
    (fun j => (hj j).2.1) (fun j => (hj j).2.2.1) (fun j => (hj j).2.2.2.2) W hW using 1
  rfl
end MultigradedFiltration
end GroundTheory.Heights₂.Heights.HilbertSamuel
