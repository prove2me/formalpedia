-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Lift_proof_87b342423455
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:04:07.957834+00:00
-- url     : https://prove2.me/submissions/fc63e5d9-9b07-4fd1-8ce6-6a83166394d5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnWLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWLift
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_twist_idealSys_eq_904493232767
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_piece_le_idealGraded_85f2dd901128
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_idealGraded_kill_499fcffa6e8e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_lift_of_subsingleton_684c811e2477
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_subsingleton_H_one_of_quot_7d14d325f023
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_subsingleton_H_one_of_smul_53085ae11a31
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_twist_idealSys_le_7910bd0d03c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_tildeSys_mono_af7572066c54


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open StepThreeOnWLift
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace StepThree.OnW.Lift
theorem _root_.solution (hSeq : ClaimSeq.Statement.{u, w}) (hVan : ClaimVanish.Statement.{u, w})
    (hTwo : StepTwo.Statement.{u, w, w}) : StepThree.OnW.Lift.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK pp hpp
  obtain ⟨Jg, hJg, hseq⟩ := hSeq k Ω N x T
  obtain ⟨cV, hV⟩ := hVan k Ω N x T hK
  have hle := piece_le_idealGraded (P := pp) hpp.1.2 Jg hJg
  obtain ⟨cS, hS⟩ := hTwo k Ω N x T hK Ω (idealGraded x pp) Jg hle (idealGraded_kill pp Jg hJg)
  refine ⟨max cS (cV - T.c₁), fun b c hb hc s hs hcomp => ?_⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hH : Subsingleton ((((T.L.pow (b' + 1)).twist (twistSys k x c)).twist (idealSys x pp)).H 1) := by
    rw [twist_idealSys_eq]
    refine SubSystem.subsingleton_H_one_of_quot _
      ((Jg.tildeSys 0).twist ((T.L.pow (b' + 1)).twist (twistSys k x c)))
      (twist_tildeSys_mono hle _) ?_ (hS (b' + 1) c (le_trans (le_max_left _ _) hc))
    exact SubSystem.subsingleton_H_one_of_smul _ _ T.si T.si_ne (hseq b' c)
      (hV b' (c + T.c₁) (by linarith [le_max_right cS (cV - T.c₁)]))
  exact lift_of_subsingleton _ _ (SurjectiveClosed.twist_idealSys_le _ pp) hH s hs hcomp
end StepThree.OnW.Lift
end GroundTheory.Heights₂.Heights.Kleiman
