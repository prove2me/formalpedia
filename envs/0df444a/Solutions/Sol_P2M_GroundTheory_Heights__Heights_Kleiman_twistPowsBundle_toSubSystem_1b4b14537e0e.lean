-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twistPowsBundle_toSubSystem_1b4b14537e0e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:16:07.061843+00:00
-- url     : https://prove2.me/submissions/0bfa19d6-a4a2-4b37-95d5-02f2aac11a9a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneMidSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_powBundle_toSubSystem_418f6a814041


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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (F : LineBundle S x) :
    ∀ (t : ℕ) (L : Fin t → LineBundle S x) (n : Fin t → ℕ),
      (twistPowsBundle F t L n).toSubSystem = F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n
  | 0, _, _ => rfl
  | t + 1, L, n => by
    change (twistPowsBundle F t (fun j => L j.castSucc) (fun j => n j.castSucc)).toSubSystem.twist
      ((L (Fin.last t)).powBundle (n (Fin.last t))).toSubSystem = _
    rw [solution F t, LineBundle.powBundle_toSubSystem]
    rfl
end GroundTheory.Heights₂.Heights.Kleiman
