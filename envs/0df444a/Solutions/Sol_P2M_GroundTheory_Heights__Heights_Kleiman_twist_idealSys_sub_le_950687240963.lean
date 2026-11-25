-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_sub_le_950687240963
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:33:42.15402+00:00
-- url     : https://prove2.me/submissions/55ba277a-419d-4861-8397-6e6b6794e041

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneMidSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_one_81e38c4bffc4

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
theorem _root_.solution (Q : SubSystem S x Ω) (J : Ideal (Poly S N)) (I : Chart x) :
    (Q.twist (idealSys x J)).sub I ≤ Q.sub I := by
  rw [SubSystem.twist_sub_eq_mul_of_line]
  exact (Submodule.mul_le.mpr fun a ha b hb => Submodule.mul_mem_mul (idealMod_le_one J I ha) hb).trans (one_mul _).le
end GroundTheory.Heights₂.Heights.Kleiman
