-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_lineNormalDivisorChartAt_1785c42bd7dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:48:39.328984+00:00
-- url     : https://prove2.me/submissions/6d11ad1b-07c3-4d0a-bfdc-199850a5d9c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eq_const_of_mem_zeroSetIn_lineDiagonal_2595c2d97644
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_const_mem_zeroSetIn_lineDiagonal_f0d6d4f27065


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology ComplexSets
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    NormalDivisorChartAt IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalModel (fun _ => (1 : ℂ)) 0 0 := by
  intro w hw hw0
  have hw' : w = 0 := by
    rw [eq_const_of_mem_zeroSetIn_lineDiagonal hw]
    have h0 : w (Sum.inl 0) = 0 := congrFun hw0 0
    funext _
    exact h0
  subst hw'
  refine ⟨1, fun t _ => t 0, 1, one_pos, Differentiable.differentiableOn (by fun_prop), ?_, rfl,
    fun t _ => IndefiniteRowSideFullHecke.ComplexSets.const_mem_zeroSetIn_lineDiagonal (t 0), ?_, ?_, ?_⟩
  · intro s _ t _ hst
    funext i
    rw [show i = 0 from Fin.ext (by omega)]
    exact congrFun hst (Sum.inl 0)
  · intro s hs
    refine ⟨Metric.ball 0 s, Metric.ball_mem_nhds 0 hs, ?_⟩
    rintro z ⟨hz, hzB⟩
    refine ⟨fun _ => z (Sum.inl 0), ?_, (eq_const_of_mem_zeroSetIn_lineDiagonal hz).symm⟩
    rw [mem_ball_zero_iff] at hzB ⊢
    refine lt_of_le_of_lt ?_ hzB
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro _
    exact norm_le_pi_norm z (Sum.inl 0)
  · refine ⟨fun _ => 1, differentiableOn_const _, fun _ _ => one_ne_zero, fun t _ => ?_⟩
    simp [linEval, IndefiniteRowSideFullHecke.ComplexSets.firstCoords]
  · intro v hv _
    funext i
    rw [show i = 0 from Fin.ext (by omega)]
    exact hv
end GroundTheory.Heights₂.Heights
