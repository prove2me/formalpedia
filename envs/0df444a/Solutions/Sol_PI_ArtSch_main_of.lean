-- Prove2me | solution 1 for PI.ArtSch.main_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:49.371863+00:00
-- url     : https://prove2.me/submissions/9e82dbe7-e4f5-4d7b-8717-ca06e6dc4888

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ArtSch
open scoped NNReal
noncomputable section
namespace PI.ArtSch
theorem _root_.solution (hW : WittLift) (hT : TiltAS) : Main := by
  intro l _ x
  exact hW l (Cb l) (hT l) x
end PI.ArtSch
