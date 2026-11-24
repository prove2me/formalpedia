-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.block_inr_inl_one
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-23T23:52:14.043667+00:00
-- url     : https://prove2.me/submissions/fa9c9ef4-ffd0-4d0c-91a4-c0696e121563

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]


theorem solution : bl Sum.inr Sum.inl (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 0 := by
  classical
  change Matrix.toEuclideanCLM (𝕜 := ℝ) ((1 : Matrix (l ⊕ l) (l ⊕ l) ℝ).submatrix Sum.inr Sum.inl) = _
  have h : (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ).submatrix Sum.inr Sum.inl = (0 : Matrix l l ℝ) := by ext i j; simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [h]; exact map_zero _
