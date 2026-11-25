-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleRing_twist_fb592b680e04
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:10:16.906546+00:00
-- url     : https://prove2.me/submissions/094a127b-8467-420c-b3d2-7bdba250125a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosedLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_mem_sub_of_mem_secs__0f08f505c152
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_twist_95103f7b6497

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
open scoped Pointwise
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
theorem _root_.solution (G H : SubSystem S x Ω) {h g : Ω} (hg : g ∈ G.secs) {u : Ω}
    (hu : u ∈ ampleRing H 1 h) : u ∈ ampleRing (G.twist H) 1 (h * g) :=
  Set.mem_iInter.mpr fun I =>
    ampleChart_twist G H I (mem_sub_of_mem_secs' hg I) (Set.mem_iInter.mp hu I)
end GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
