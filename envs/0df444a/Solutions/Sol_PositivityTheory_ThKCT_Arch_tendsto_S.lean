-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.tendsto_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:39:25.068365+00:00
-- url     : https://prove2.me/submissions/cd4b9aa8-cbcf-4e5e-af91-83f87617e57c

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_lip

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
theorem _root_.solution (f : SchwartzMap V ℂ) : Tendsto (fun w => S w f) (𝓝 0) (𝓝 f) := by
  rw [(schwartz_withSeminorms ℂ V ℂ).tendsto_nhds]
  intro i ε hε
  obtain ⟨p, -, hp⟩ := lip _ ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i)
  have h1 : Tendsto (fun w : V × (V →L[ℝ] ℝ) => ‖w‖ * p f) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_norm_zero (E := V × (V →L[ℝ] ℝ))).mul_const (p f)
  filter_upwards [h1.eventually (gt_mem_nhds hε), Metric.closedBall_mem_nhds 0 one_pos] with w h2 h3
  exact (hp w f (by simpa using h3)).trans_lt h2
end PositivityTheory.ThKCT.Arch
