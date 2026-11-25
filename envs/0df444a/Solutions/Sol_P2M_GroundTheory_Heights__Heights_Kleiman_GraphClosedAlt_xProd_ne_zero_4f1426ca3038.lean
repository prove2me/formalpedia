-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_xProd_ne_zero_4f1426ca3038
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:14:01.437913+00:00
-- url     : https://prove2.me/submissions/d9a221ef-6a7d-428b-ad48-867a9a17a5d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosedLocal

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
open GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
theorem _root_.solution (I : Chart x) : xProd I ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hi => (mem_support x).mp (I.2.2 hi)
end GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
