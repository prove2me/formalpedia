-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.S_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:27.021907+00:00
-- url     : https://prove2.me/submissions/4892fc81-0353-429a-9d08-75f0260689de

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_S_apply

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
theorem _root_.solution (w h : V × (V →L[ℝ] ℝ)) (f : SchwartzMap V ℂ) :
    S (w + h) f = cexp (I * ((w.2 h.1 - h.2 w.1) / 2 : ℝ)) • S w (S h f) := by
  ext x
  rw [SchwartzMap.smul_apply, S_apply, S_apply, S_apply, ph, ph, ph, smul_eq_mul, ← mul_assoc, ← mul_assoc, ← Complex.exp_add,
    ← Complex.exp_add, Prod.fst_add, add_assoc x]
  congr 2
  simp only [Prod.snd_add, ContinuousLinearMap.add_apply, map_add]
  push_cast
  ring
end PositivityTheory.ThKCT.Arch
