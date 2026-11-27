-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_twistPows_eq_1c2add2714bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:03:47.737533+00:00
-- url     : https://prove2.me/submissions/fb20b349-570c-46f0-aef0-3a9f5ccbb4f7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_HomogeneousComponentMulForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_twist_twist_a941cbd44f76
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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
theorem _root_.solution (F : SubSystem S x E) : ∀ (t : ℕ) (L : Fin t → LineBundle S x) (n : Fin t → ℕ),
    F.twistPows t (fun j => (L j).toSubSystem) n = F.twist (powsBundle t L n).toSubSystem
  | 0, _, _ => by
    change F = F.twist (twistSys S x 0)
    rw [SubSystem.twist_twistSys_zero]
  | t + 1, L, n => by
    change (F.twistPows t (fun j => (L j.castSucc).toSubSystem) (fun j => n j.castSucc)).twist
      (((L (Fin.last t)).toSubSystem).pow (n (Fin.last t))) = _
    rw [solution F t, twist_twist, ← LineBundle.powBundle_toSubSystem]
    rfl
end GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
