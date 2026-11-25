-- Prove2me | solution 1 for PositivityTheory.ThKEst.LinDerPf.Gr.anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:14.157797+00:00
-- url     : https://prove2.me/submissions/3ac7d532-7ed3-4246-8d4b-b5150260c303

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
theorem _root_.solution (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) {g : A} (hg : Gr a g) :
    a (pr a g) = -pr a g := by
  have h2 : a g * a (a g) = 1 := by rw [← ha, hg.1, h1]
  have h3 : a (a g) = g := by
    calc a (a g) = (g * a g) * a (a g) := by rw [hg.2, one_mul]
      _ = g := by rw [mul_assoc, h2, mul_one]
  rw [pr_apply, map_smul, map_sub, h3, ← smul_neg, neg_sub]
end Gr
end PositivityTheory.ThKEst.LinDerPf
