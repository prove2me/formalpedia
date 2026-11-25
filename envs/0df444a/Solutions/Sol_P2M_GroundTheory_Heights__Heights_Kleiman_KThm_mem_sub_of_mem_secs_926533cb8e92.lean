-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KThm_mem_sub_of_mem_secs_926533cb8e92
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:59:00.094699+00:00
-- url     : https://prove2.me/submissions/b0bcae38-35b8-4e8d-98ce-cdf7d8be3844

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple

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
theorem _root_.solution {F : SubSystem S x Ω} {z : Ω} (hz : z ∈ F.secs) (I : Chart x) :
    z ∈ F.sub I := by
  rw [SubSystem.secs, Submodule.mem_iInf] at hz
  exact hz I
end KThm
end GroundTheory.Heights₂.Heights.Kleiman
