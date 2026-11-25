-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_res_aeval_prod_X_04ef03c50aaa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:29:58.409662+00:00
-- url     : https://prove2.me/submissions/cd9b07ed-b6ba-4fc1-9c7a-803203f1ca54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers

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
theorem _root_.solution (s : Finset (Fin (N + 1))) :
    aeval x (∏ i ∈ s, (X i : Poly S N)) = ∏ i ∈ s, x i := by
  simp [map_prod]
end GroundTheory.Heights₂.Heights.Kleiman
