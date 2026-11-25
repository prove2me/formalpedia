-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermsNoetherian_proof_bbc29778fca7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:08:10.658831+00:00
-- url     : https://prove2.me/submissions/970d4de3-ded4-4afb-b18d-a2e1f5000996

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermGeneralCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermsNoetherian
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isNoetherianRing_holGerms_transfer_2456715cee76
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isField_holGerms_fin_zero_e759378e8bfd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isNoetherianRing_holGerms_option_226d87cbc67c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace AnalyticGermsNoetherian
theorem _root_.solution (hD : WeierstrassDivision.Statement)
    (hG : GeneralLinearCoordinates.Statement) : AnalyticGermsNoetherian.Statement := by
  have hfin : ∀ n : ℕ, IsNoetherianRing (holGerms (0 : Fin n → ℂ)) := by
    intro n
    induction n with
    | zero =>
      let _ := (isField_holGerms_fin_zero).toField
      infer_instance
    | succ n ih =>
      have h := isNoetherianRing_holGerms_option hD hG (Fin n) ih
      exact isNoetherianRing_holGerms_transfer
        (LinearEquiv.funCongrLeft ℂ ℂ (finSuccEquiv n)).toContinuousLinearEquiv 0 h
  intro σ _ w
  exact isNoetherianRing_holGerms_transfer
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ)).toContinuousLinearEquiv w (hfin _)
end AnalyticGermsNoetherian
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
