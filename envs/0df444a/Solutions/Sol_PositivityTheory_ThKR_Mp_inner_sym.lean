-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.inner_sym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:37:37.415028+00:00
-- url     : https://prove2.me/submissions/b170c753-cb21-4851-af63-725e76f24c32

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_PositivityTheory_ThKR_Mp_tc_apply

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
theorem _root_.solution {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (x y : Eu l) :
    ⟪x, (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) y⟫ =
      ⟪y, (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) x⟫ := by
  have hS' : ∀ a b, S a b = S b a := fun a b => by
    simpa using (congrFun (congrFun hS.eq b) a)
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, inner_neg_right, real_inner_smul_right]
  congr 2
  simp only [PiLp.inner_apply, tc_apply, RCLike.inner_apply, conj_trivial, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hS']
  ring
end PositivityTheory.ThKR.Mp
