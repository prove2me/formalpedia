-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_twistSys_nat_4a88fe4e3490
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:45.720594+00:00
-- url     : https://prove2.me/submissions/4fa586b2-7de7-4398-9bd7-751eb77bf379

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_sub_pow_a678e760a862
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_pow_d59270f20e61
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_pow_f814712537f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_twistSys_one_94b99c7842cc

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace KThm
theorem _root_.solution (e : ℕ) : (twistSys S x e).Generated := by
  have h : twistSys S x e = (twistSys S x 1).pow e := by
    refine SubSystem.ext_sub fun I => ?_
    obtain ⟨i, hi⟩ := I.2.1
    rw [KThm.sub_pow]
    change twistMod S x e I = twistMod S x 1 I ^ e
    rw [twistMod_eq_span _ I hi, twistMod_eq_span _ I hi, KThm.span_zpow_pow I hi, one_mul]
  rw [h]
  exact KThm.generated_pow KThm.generated_twistSys_one e
end KThm
end GroundTheory.Heights₂.Heights.Kleiman
