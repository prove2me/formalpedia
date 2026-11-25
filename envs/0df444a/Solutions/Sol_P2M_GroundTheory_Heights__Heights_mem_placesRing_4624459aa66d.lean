-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_placesRing_4624459aa66d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:35:45.055378+00:00
-- url     : https://prove2.me/submissions/a3c43bfe-12b9-4779-84e2-2c88059a75a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlacesRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {L : Type*} [Field L] [NumberField L] (S : Set (FinitePlace L)) (x : L) :
    x ∈ placesRing S ↔ ∀ w ∈ S, w x ≤ 1 := Iff.rfl
end GroundTheory.Heights₂.Heights
