-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechTop_idx_isEmpty_10e419feb8ed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:01:39.952748+00:00
-- url     : https://prove2.me/submissions/e98b2726-d1ef-45e9-a558-f95ccfe04fdb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTop

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
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace CechTop
theorem _root_.solution (N i : ℕ) (hi : N < i) :
    IsEmpty (Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) := by
  refine ⟨fun I => ?_⟩
  have h1 : I.1.1.card ≤ N + 1 := by
    simpa using Finset.card_le_univ I.1.1
  have h2 := I.2
  omega
end CechTop
end GroundTheory.Heights₂.Heights.Kleiman
