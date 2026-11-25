-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.qd_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:32:27.211345+00:00
-- url     : https://prove2.me/submissions/aba43316-67c7-4005-8755-ec3e63b052f8

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MpFOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real ContDiff RealInnerProductSpace
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKR.Mp
theorem _root_.solution (X : Mat l) (f : Sch l) : ∑ a, ∑ b, X a b • Qd (Matrix.single a b 1) f = Qd X f := by
  show _ = qdLin f X
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [show Matrix.single a b (X a b) = X a b • Matrix.single a b (1 : ℝ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul]
  rfl
end PositivityTheory.ThKR.Mp
