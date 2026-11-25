-- Prove2me | solution 1 for PositivityTheory.ThKEst.LinDerPf.Gr.list
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:09.667976+00:00
-- url     : https://prove2.me/submissions/b1163c13-1b1e-4408-8c2d-2fd130d233f3

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_LinDerA
import Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_Gr_mul

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
theorem _root_.solution (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) (l : List A) (hl : ∀ g ∈ l, Gr a g) :
    Gr a l.prod := by
  induction l with
  | nil => simp [Gr, h1]
  | cons x l ih =>
    rw [List.prod_cons]
    exact (hl x (by simp)).mul ha (ih fun g hg => hl g (by simp [hg]))
end Gr
end PositivityTheory.ThKEst.LinDerPf
