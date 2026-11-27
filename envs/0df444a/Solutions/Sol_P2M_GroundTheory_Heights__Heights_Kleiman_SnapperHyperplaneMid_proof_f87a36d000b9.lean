-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_proof_f87a36d000b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:02:33.972846+00:00
-- url     : https://prove2.me/submissions/31c2f605-efb7-4292-a939-9e9205d332d7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplaneMid
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_eulerCharQuot_mid_6a0fa6ff4b63
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_assoc_e501c3cc2859
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_comm_31b97c8bd736
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistPowsBundle_toSubSystem_1b4b14537e0e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistPows_twist_comm_3dd36e957fe6
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
namespace SnapperHyperplaneMid
theorem _root_.solution : SnapperHyperplaneMid.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp hp hh hle i hi a t L n c
  let Mb := (twistPowsBundle (twistBundle k x a) t L n).tensorProd (twistBundle k x c)
  have hM : Mb.toSubSystem =
      ((twistSys k x a).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c) := by
    change (twistPowsBundle (twistBundle k x a) t L n).toSubSystem.twist (twistSys k x c) = _
    rw [twistPowsBundle_toSubSystem]
    rfl
  have hG : ∀ (b : ℤ) (K : Ideal (Poly k N)),
      (((twistSys k x b).twist (idealSys x K)).twistPows t (fun j => (L j).toSubSystem) n).twist
          (twistSys k x c) =
        (((twistSys k x b).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c)).twist
          (idealSys x K) := by
    intro b K
    rw [twistPows_twist_comm (twistSys k x b) (idealSys x K), SubSystem.twist_assoc,
      SubSystem.twist_comm (idealSys x K), ← SubSystem.twist_assoc]
  have hQ : ((twistSys k x (a + 1)).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c) =
      Mb.toSubSystem.twist (twistSys k x 1) := by
    rw [hM, ← twistSys_twist_eq_add a 1, twistPows_twist_comm (twistSys k x a) (twistSys k x 1),
      SubSystem.twist_assoc _ (twistSys k x 1) (twistSys k x c),
      SubSystem.twist_comm (twistSys k x 1) (twistSys k x c), ← SubSystem.twist_assoc]
  unfold pieceChar
  rw [hG (a + 1) (pp ⊔ Ideal.span {(X i : Poly k N)}), hG (a + 1) pp, hG a pp, hQ, ← hM]
  exact SnapperHyperplaneMid.eulerCharQuot_mid pp hp hh hle i hi Mb.toSubSystem Mb.invertible
end SnapperHyperplaneMid
end GroundTheory.Heights₂.Heights.Kleiman
