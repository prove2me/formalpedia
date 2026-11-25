-- Prove2me | solution 1 for ReciprocityTheory.Coh.low_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:02:12.354525+00:00
-- url     : https://prove2.me/submissions/bf2a932d-35d1-4bf4-b120-548b638e251d

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ComapZeroCoboundariesEqBot
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Theorems.Thm_ReciprocityTheory_Coh_LowDeg_cohomZeroEquivContinuous_cls_apply
import Theorems.Thm_ReciprocityTheory_Coh_LowDeg_hEquiv_cls


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
universe u
namespace ReciprocityTheory.Coh
theorem _root_.solution : LowStatement.{u} := by
  intro R _ G _ _ _ M
  refine ⟨fun n => ⟨LowDeg.hEquiv M n, fun x hx => ⟨_, LowDeg.hEquiv_cls M n x hx⟩⟩,
    ⟨LowDeg.cohomZeroEquivContinuous M, fun x hx => LowDeg.cohomZeroEquivContinuous_cls_apply M x hx⟩,
    ⟨LowDeg.h1EquivOfOrderTwo M, fun x hx => ⟨_, rfl⟩⟩, ⟨LowDeg.h2EquivOfOrderTwo M, fun x hx => ⟨_, rfl⟩⟩⟩
end ReciprocityTheory.Coh
