-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_sub_mono_40ccbdb422bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:07.169906+00:00
-- url     : https://prove2.me/submissions/b879a321-05a6-4b73-92c1-511a85f0a5d9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneMidSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_of_le_49d75206baab

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
theorem _root_.solution (Q : SubSystem S x Ω) {J J' : Ideal (Poly S N)} (h : J ≤ J') (I : Chart x) :
    (Q.twist (idealSys x J)).sub I ≤ (Q.twist (idealSys x J')).sub I := by
  rw [SubSystem.twist_sub_eq_mul_of_line, SubSystem.twist_sub_eq_mul_of_line]
  exact Submodule.mul_le.mpr fun a ha b hb => Submodule.mul_mem_mul (idealMod_le_of_le h I ha) hb
end GroundTheory.Heights₂.Heights.Kleiman
