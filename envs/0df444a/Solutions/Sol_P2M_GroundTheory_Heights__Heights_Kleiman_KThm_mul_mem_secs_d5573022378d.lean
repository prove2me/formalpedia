-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KThm_mul_mem_secs_d5573022378d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:13:22.771453+00:00
-- url     : https://prove2.me/submissions/2378f50d-1e8b-473e-956f-c9923774d268

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_mem_sub_of_mem_secs_926533cb8e92

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
theorem _root_.solution {F Q : SubSystem S x Ω} {a b : Ω} (ha : a ∈ F.secs) (hb : b ∈ Q.secs) :
    b * a ∈ (F.twist Q).secs := by
  rw [SubSystem.secs, Submodule.mem_iInf]
  intro I
  exact Submodule.subset_span ⟨b, KThm.mem_sub_of_mem_secs hb I, a, KThm.mem_sub_of_mem_secs ha I,
    (smul_eq_mul b a).symm⟩
end KThm
end GroundTheory.Heights₂.Heights.Kleiman
