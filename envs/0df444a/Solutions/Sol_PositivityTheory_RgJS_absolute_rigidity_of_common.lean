-- Prove2me | solution 1 for PositivityTheory.RgJS.absolute_rigidity_of_common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:22.645915+00:00
-- url     : https://prove2.me/submissions/5b5c88ab-fb7a-4361-9ac8-f361678a1c3f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_AbsoluteRigidityLemma_AbsoluteRigidityOfCommon
import Theorems.Thm_PositivityTheory_RgJS_AbsoluteRigidity_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgJS
namespace PositivityTheory.RgJS
theorem _root_.solution : Common0 → AbsRig := by
  intro hC W q X d A hS ι κ _ _ x y h
  exact AbsoluteRigidity.main hC hS _ ι κ x y le_rfl h
end PositivityTheory.RgJS
