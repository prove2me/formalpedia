-- Prove2me | solution 1 for PositivityTheory.ThKEst.LinDerPf.Gr.eq_of_pr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:20.991051+00:00
-- url     : https://prove2.me/submissions/aa823129-d7b6-4ac6-9905-cb2bea9ff435

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_LinDerA
import Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_pr_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.LinDerPf
open Filter Topology Asymptotics
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {a : A →L[ℝ] A}
namespace PositivityTheory.ThKEst.LinDerPf
namespace Gr
theorem _root_.solution {g h : A} (hg : Gr a g) (hh : Gr a h) (h1 : ‖1 - a g‖ ≤ 1 / 2) (h2 : ‖1 - a h‖ ≤ 1 / 2)
    (e : pr a g = pr a h) : g = h := by
  have e1 : g - a g = h - a h := by
    have := congrArg (fun x => (2 : ℝ) • x) e
    simpa [pr_apply, smul_smul] using this
  set D := g - h with hD
  have e2 : a g * D * a h = -D := by
    rw [hD, mul_sub, sub_mul, hg.1, one_mul, mul_assoc, hh.2, mul_one]
    have : a h = h - (g - a g) := by rw [e1]; abel
    rw [this]; abel
  have e3 : (2 : ℝ) • D = (1 - a g) * D + D * (1 - a h) - (1 - a g) * D * (1 - a h) := by
    have : (1 - a g) * D + D * (1 - a h) - (1 - a g) * D * (1 - a h) = D - a g * D * a h := by noncomm_ring
    rw [this, e2, two_smul, sub_neg_eq_add]
  have n1 : ‖(1 - a g) * D‖ ≤ 1 / 2 * ‖D‖ := (norm_mul_le _ _).trans (by gcongr)
  have n2 : ‖D * (1 - a h)‖ ≤ ‖D‖ * (1 / 2) := (norm_mul_le _ _).trans (by gcongr)
  have n3 : ‖(1 - a g) * D * (1 - a h)‖ ≤ 1 / 2 * ‖D‖ * (1 / 2) := (norm_mul_le _ _).trans (by gcongr)
  have n4 : 2 * ‖D‖ ≤ ‖(1 - a g) * D‖ + ‖D * (1 - a h)‖ + ‖(1 - a g) * D * (1 - a h)‖ := by
    have : ‖(2 : ℝ) • D‖ = 2 * ‖D‖ := by rw [norm_smul]; norm_num
    rw [← this, e3]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  have : ‖D‖ ≤ 0 := by linarith
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
end Gr
end PositivityTheory.ThKEst.LinDerPf
