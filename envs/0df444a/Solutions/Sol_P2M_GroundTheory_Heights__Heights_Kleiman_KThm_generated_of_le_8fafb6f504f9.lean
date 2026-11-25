-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_of_le_8fafb6f504f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:14:07.247036+00:00
-- url     : https://prove2.me/submissions/f186b581-a7c9-4c40-95a1-91e453b3c92d

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
theorem _root_.solution (F : SubSystem S x Ω)
    (h : ∀ I, F.sub I ≤ Submodule.span (chartRing S x I) (F.secs : Set Ω)) : F.Generated := by
  intro I
  refine le_antisymm (Submodule.span_le.mpr fun z hz => ?_) (h I)
  exact KThm.mem_sub_of_mem_secs hz I
end KThm
end GroundTheory.Heights₂.Heights.Kleiman
