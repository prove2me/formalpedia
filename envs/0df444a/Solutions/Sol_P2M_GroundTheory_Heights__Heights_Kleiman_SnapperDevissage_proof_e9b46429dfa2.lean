-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDevissage_proof_e9b46429dfa2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:36:05.910601+00:00
-- url     : https://prove2.me/submissions/9e501103-9419-461b-9d15-9d82d14fa80a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_eq_bot_cb2151b2317a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistPows_sub_eq_bot_405b85e0afc3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_primeOf_sub_9fa796ef3d4e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_eulerCharQuot_of_bot_8adbac9f88d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_mem_primeOf_077b7ab281b2


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
universe u v w u₁ v₁ w₁
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SnapperDevissage
theorem _root_.solution (hQ : SnapperQuotDevissage.Statement.{u, v, w}) :
    SnapperDevissage.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F hF
  obtain ⟨r, pp, a, hpp, heq⟩ := hQ k Ω N x E F (zeroFamily k x E) hF (fun _ => bot_le)
    (primeOf (S := k) x) (fun f hf d => homogeneousComponent_mem_primeOf x hf d) le_rfl
    (fun I => (twist_idealSys_primeOf_sub F.toSubSystem I).le)
  refine ⟨r, pp, a, hpp, fun t L n c => ?_⟩
  rw [← heq t L n c]
  exact (eulerCharQuot_of_bot _ _ fun I =>
    twist_sub_eq_bot (twistPows_sub_eq_bot (fun _ => rfl) t _ n) _ I).symm
end SnapperDevissage
end GroundTheory.Heights₂.Heights.Kleiman
