-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_level_b7e577dac56b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:54:55.374648+00:00
-- url     : https://prove2.me/submissions/2dc1412d-7015-4382-8eb8-5099663477f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision

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
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open MeasureTheory
namespace GroundTheory.Heights₂.Heights.EffectiveHS
theorem _root_.solution (D T a : ℕ) (hD : 1 ≤ D) (ha : a + D + 1 ≤ T) :
    D + 1 ≤ T - a ∧ 2 ≤ D + 1 := by omega
end GroundTheory.Heights₂.Heights.EffectiveHS
