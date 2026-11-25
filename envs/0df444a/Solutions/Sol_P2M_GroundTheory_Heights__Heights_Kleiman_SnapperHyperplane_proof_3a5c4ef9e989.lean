-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplane_proof_3a5c4ef9e989
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:57:32.660244+00:00
-- url     : https://prove2.me/submissions/9ee2b268-a889-465b-a3e4-099bbf4d1a76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneMidSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistPows_twist_comm_3dd36e957fe6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistPowsBundle_toSubSystem_1b4b14537e0e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_sub_le_950687240963
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_sub_mono_40ccbdb422bc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_sup_span_X_homogeneous_29e7ce851657
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_twist_mem_iff_e4733d843f95
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_assoc_e501c3cc2859
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_comm_31b97c8bd736
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_twist_eq_add_659a52088064


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
namespace SnapperHyperplane
theorem _root_.solution (hA : SnapperQuotAdd.Statement.{u, w, w})
    (hD : SnapperQuotDevissage.Statement.{u, w, w}) (hM : SnapperHyperplaneMid.Statement.{u, w}) :
    SnapperHyperplane.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp hp hh hle i hi a
  set J : Ideal (Poly k N) := pp ⊔ Ideal.span {(X i : Poly k N)} with hJdef
  let B := twistBundle k x (a + 1)
  let F₂ : SubFamily k x Ω :=
    { B.twist (idealSys x J) with mem_iff := IdealTwistFamily.twist_mem_iff B J }
  obtain ⟨r, qq, b, hqq, heq⟩ := hD k Ω N x Ω B.toSubFamily F₂ B.fg
    (fun I => twist_idealSys_sub_le B.toSubSystem J I) J (sup_span_X_homogeneous pp hh i)
    (hle.trans le_sup_left) (fun I => le_rfl)
  refine ⟨r, qq, b, fun m => ⟨(hqq m).1, (hqq m).2.1, le_sup_left.trans (hqq m).2.2,
    (hqq m).2.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩, fun t L n c => ?_⟩
  let Q := (twistPowsBundle B t L n).tensorProd (twistBundle k x c)
  have hQ : Q.toSubSystem =
      ((twistSys k x (a + 1)).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c) := by
    change (twistPowsBundle B t L n).toSubSystem.twist (twistSys k x c) = _
    rw [twistPowsBundle_toSubSystem]
    rfl
  have hG : ∀ K : Ideal (Poly k N),
      (((twistSys k x (a + 1)).twist (idealSys x K)).twistPows t (fun j => (L j).toSubSystem) n).twist
        (twistSys k x c) = Q.toSubSystem.twist (idealSys x K) := by
    intro K
    rw [hQ, twistPows_twist_comm (twistSys k x (a + 1)) (idealSys x K), SubSystem.twist_assoc,
      SubSystem.twist_comm (idealSys x K), ← SubSystem.twist_assoc]
  let G₂ : SubFamily k x Ω := { Q.twist (idealSys x J) with mem_iff := IdealTwistFamily.twist_mem_iff Q J }
  let G₃ : SubFamily k x Ω := { Q.twist (idealSys x pp) with mem_iff := IdealTwistFamily.twist_mem_iff Q pp }
  have hadd : eulerCharQuot k Q.toSubSystem (Q.toSubSystem.twist (idealSys x pp)) =
      eulerCharQuot k Q.toSubSystem (Q.toSubSystem.twist (idealSys x J)) +
        eulerCharQuot k (Q.toSubSystem.twist (idealSys x J)) (Q.toSubSystem.twist (idealSys x pp)) :=
    hA k Ω N x Ω Q.toSubFamily G₂ G₃ Q.fg (fun I => twist_idealSys_sub_le Q.toSubSystem J I)
      (fun I => twist_idealSys_sub_mono Q.toSubSystem le_sup_left I)
  have h1 : pieceChar k pp a L n (c + 1) =
      eulerCharQuot k Q.toSubSystem (Q.toSubSystem.twist (idealSys x pp)) := by
    have eA : ((twistSys k x a).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x (c + 1)) =
        Q.toSubSystem := by
      rw [hQ, ← twistSys_twist_eq_add a 1,
        twistPows_twist_comm (twistSys k x a) (twistSys k x 1), SubSystem.twist_assoc,
        twistSys_twist_eq_add, add_comm 1 c]
    have eB : (((twistSys k x a).twist (idealSys x pp)).twistPows t (fun j => (L j).toSubSystem) n).twist
        (twistSys k x (c + 1)) = Q.toSubSystem.twist (idealSys x pp) := by
      rw [← hG pp, ← twistSys_twist_eq_add a 1, SubSystem.twist_assoc (twistSys k x a),
        SubSystem.twist_comm (twistSys k x 1), ← SubSystem.twist_assoc (twistSys k x a),
        twistPows_twist_comm ((twistSys k x a).twist (idealSys x pp)) (twistSys k x 1),
        SubSystem.twist_assoc _ (twistSys k x 1), twistSys_twist_eq_add, add_comm 1 c]
    unfold pieceChar
    rw [eA, eB]
  have h2 : eulerCharQuot k Q.toSubSystem (Q.toSubSystem.twist (idealSys x J)) =
      ∑ m, pieceChar k (qq m) (b m) L n c := by
    have := heq t L n c
    change eulerCharQuot k
      (((twistSys k x (a + 1)).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
      ((((twistSys k x (a + 1)).twist (idealSys x J)).twistPows t (fun j => (L j).toSubSystem) n).twist
        (twistSys k x c)) = _ at this
    rwa [hG J, ← hQ] at this
  have h3 := hM k Ω N x pp hp hh hle i hi a t L n c
  rw [← hJdef, hG J, hG pp] at h3
  rw [h1, hadd, h2, h3]
  ring
end SnapperHyperplane
end GroundTheory.Heights₂.Heights.Kleiman
