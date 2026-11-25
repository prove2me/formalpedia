-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.u_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:00:09.762135+00:00
-- url     : https://prove2.me/submissions/012ebbb2-b6cf-4c94-8e13-1f76af71a80f

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_succ

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
theorem _root_.solution (c : ℝ) (i : ℕ) :
    iteratedDeriv i (fun s : ℝ => cexp (I * ((s + c : ℝ) : ℂ))) = fun s : ℝ => I ^ i * cexp (I * ((s + c : ℝ) : ℂ)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    have h : HasDerivAt (fun s : ℝ => ((s + c : ℝ) : ℂ)) 1 s := ((hasDerivAt_id s).add_const c).ofReal_comp
    rw [(((h.const_mul I).cexp).const_mul (I ^ i)).deriv]
    ring
end PositivityTheory.ThKCT.Arch
