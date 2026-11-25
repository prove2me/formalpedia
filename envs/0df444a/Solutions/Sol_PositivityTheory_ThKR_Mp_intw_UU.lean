-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.intw_UU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:37.567845+00:00
-- url     : https://prove2.me/submissions/5fb61c9b-2128-45d3-befb-fe9045442b23

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_PositivityTheory_ThKR_Mp_inner_sym
import Theorems.Thm_PositivityTheory_ThKR_LL_Intw_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_Iso_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_LD_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_intw_fou
import Theorems.Thm_PositivityTheory_ThKR_LL_intw_fouInv
import Theorems.Thm_PositivityTheory_ThKR_LL_intw_ph


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKR.Mp
theorem _root_.solution {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (p q : Eu l) :
    Intw (UU S t) p q (p + (t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S) q) q := by
  have h := (intw_fou _ _).mul ((intw_ph (inner_sym hS t) _ _).mul (intw_fouInv p q))
  rw [show p + (t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S) q =
    -(-p + (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) q) by
      rw [ContinuousLinearMap.neg_apply, neg_add, neg_neg, neg_neg]]
  exact h
end PositivityTheory.ThKR.Mp
