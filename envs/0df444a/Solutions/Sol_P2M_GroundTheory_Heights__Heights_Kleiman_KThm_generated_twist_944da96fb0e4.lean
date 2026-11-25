-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_twist_944da96fb0e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:24:34.304889+00:00
-- url     : https://prove2.me/submissions/66dd8086-9df9-4e38-9345-05371d1f03fd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_of_le_8fafb6f504f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_mul_mem_secs_d5573022378d

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
theorem _root_.solution {F Q : SubSystem S x Ω} (hF : F.Generated) (hQ : Q.Generated) :
    (F.twist Q).Generated := by
  refine KThm.generated_of_le _ fun I => ?_
  rw [KThm.sub_twist, ← hF I, ← hQ I, Submodule.span_mul_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨b, hb, a, ha, rfl⟩
  exact KThm.mul_mem_secs ha hb
end KThm
end GroundTheory.Heights₂.Heights.Kleiman
