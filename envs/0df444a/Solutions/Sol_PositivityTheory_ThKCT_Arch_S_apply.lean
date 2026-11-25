-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.S_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:12.271871+00:00
-- url     : https://prove2.me/submissions/54f15965-95d9-4810-bfc9-9efa09b1cade

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_ph_temp

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
theorem _root_.solution (w : V × (V →L[ℝ] ℝ)) (f : SchwartzMap V ℂ) (x : V) : S w f x = ph w.2 (w.2 w.1 / 2) x * f (x + w.1) := by
  rw [S, ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply (ph_temp _ _), SchwartzMap.compSubConstCLM_apply,
    sub_neg_eq_add, smul_eq_mul]
end PositivityTheory.ThKCT.Arch
