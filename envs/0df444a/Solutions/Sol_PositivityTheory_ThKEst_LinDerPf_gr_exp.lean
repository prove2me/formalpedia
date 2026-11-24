-- Prove2me | solution 1 for PositivityTheory.ThKEst.LinDerPf.gr_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:32:42.425678+00:00
-- url     : https://prove2.me/submissions/5fe48b68-5b64-4cc4-9b5a-376cccaafd4b

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_LinDerA

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
theorem _root_.solution [CompleteSpace A] (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) {Y : A} (hY : a Y = -Y) :
    Gr a (NormedSpace.exp Y) := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let φ : A →+* Aᵐᵒᵖ :=
    { toFun := fun x => MulOpposite.op (a x)
      map_one' := by rw [h1]; rfl
      map_mul' := fun x y => by rw [ha]; rfl
      map_zero' := by rw [map_zero]; rfl
      map_add' := fun x y => by rw [map_add]; rfl }
  have h2 := NormedSpace.map_exp φ (MulOpposite.continuous_op.comp a.continuous) Y
  have h3 : a (NormedSpace.exp Y) = NormedSpace.exp (-Y) := by
    apply MulOpposite.op_injective
    rw [← hY, ← NormedSpace.exp_op]
    exact h2
  constructor
  · rw [h3, ← NormedSpace.exp_add_of_commute (Commute.refl Y).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  · rw [h3, ← NormedSpace.exp_add_of_commute (Commute.refl Y).neg_right, add_neg_cancel, NormedSpace.exp_zero]
end PositivityTheory.ThKEst.LinDerPf
