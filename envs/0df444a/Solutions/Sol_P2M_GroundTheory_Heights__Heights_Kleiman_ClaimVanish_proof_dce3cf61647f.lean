-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ClaimVanish_proof_dce3cf61647f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:20:03.168249+00:00
-- url     : https://prove2.me/submissions/c81627e9-396a-4c62-b56a-4063503525bb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_tildeSys_twist_dbe5ec796d37
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_tildeSys_mono_af7572066c54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_claim_le_346deb24d81f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_claim_kill_e71d0cb7bfe0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_subsingleton_H_one_of_quot_7d14d325f023
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_subsingleton_H_one_of_smul_53085ae11a31
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_hyps_bc69208ec540


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
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace ClaimVanish
theorem _root_.solution (h₁ : StepTwo.Statement.{u, w, w}) (h₂ : TwistVanish.Statement.{u, w})
    (h₃ : ClaimSeq.Statement.{u, w}) : ClaimVanish.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK
  obtain ⟨Jg, hJg, hseq⟩ := h₃ k Ω N x T
  obtain ⟨cS, hS⟩ := h₁ k Ω N x T hK Ω (coordGraded k x) Jg (claim_le T Jg hJg)
    (claim_kill T Jg hJg)
  obtain ⟨cB, hB⟩ := h₂ k Ω N x (twistBundle k x 0) (twistBundle k x 1) N x (twist_hyps k N x).1
    (twist_hyps k N x).2
  refine ⟨max cS cB, fun b => ?_⟩
  induction b with
  | zero =>
    intro c hc
    have h0 := hB 0 c (le_trans (le_max_right _ _) hc)
    have e : ((twistBundle k x 0).twist ((twistBundle k x 1).pow 0)).twist (twistSys k x c) =
        (T.L.pow 0).twist (twistSys k x c) := by
      show ((twistSys k x 0).twist (twistSys k x 0)).twist (twistSys k x c) =
        (twistSys k x 0).twist (twistSys k x c)
      rw [twistSys_zero_twist]
    rw [e] at h0
    exact h0
  | succ b ih =>
    intro c hc
    have hq := hS (b + 1) c (le_trans (le_max_left _ _) hc)
    rw [coordGraded_tildeSys_twist] at hq
    refine SubSystem.subsingleton_H_one_of_quot _
      ((Jg.tildeSys 0).twist ((T.L.pow (b + 1)).twist (twistSys k x c))) ?_ ?_ hq
    · intro I y hy
      have hy' := twist_tildeSys_mono (claim_le T Jg hJg) _ I y hy
      rwa [coordGraded_tildeSys_twist] at hy'
    · exact SubSystem.subsingleton_H_one_of_smul _ _ T.si T.si_ne (hseq b c)
        (ih (c + T.c₁) (le_trans hc (by linarith [T.c₁_pos])))
end ClaimVanish
end GroundTheory.Heights₂.Heights.Kleiman
