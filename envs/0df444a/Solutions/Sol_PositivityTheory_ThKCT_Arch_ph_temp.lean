-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.ph_temp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:13.626176+00:00
-- url     : https://prove2.me/submissions/18b8dbf1-8052-4b98-ac7f-25998492ef8c

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_ph_smooth
import Theorems.Thm_PositivityTheory_ThKCT_Arch_ph_bd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Arch
open scoped ContDiff NNReal
open Complex Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace PositivityTheory.ThKCT.Arch
theorem _root_.solution (l : V →L[ℝ] ℝ) (c : ℝ) : (ph l c).HasTemperateGrowth :=
  ⟨ph_smooth l c, fun n => ⟨0, ‖l‖ ^ n, fun x => by simpa using ph_bd l c n x⟩⟩
end PositivityTheory.ThKCT.Arch
