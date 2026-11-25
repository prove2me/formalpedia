-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_pow_add_le_mul_ff1e09ec03ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:13:45.731803+00:00
-- url     : https://prove2.me/submissions/b6901cc6-7355-451a-a563-ddab359b68ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropHilbWSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDrop

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
open Filter
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop
theorem _root_.solution (c n : ℝ) (hc : 0 ≤ c) (hn : 1 ≤ n) (e : ℕ) :
    (n + c) ^ e ≤ (1 + c) ^ e * n ^ e := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by linarith) (by nlinarith) e
end GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop
