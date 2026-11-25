-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_ball_indicator_le_6727de79cc83
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:38:28.319125+00:00
-- url     : https://prove2.me/submissions/0791cd56-28bf-4631-81d2-a81a6bd72e94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_linProj_smul_firstCoordVec_862aecb3e19a

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
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail
namespace GroundTheory.Heights₂.Heights.LeadBlockGaussTail
theorem _root_.solution {m n : ℕ} (π : Fin m → Fin n → ℂ) (r : ℝ) (c0 : Fin n)
    (hc0 : (c0 : ℕ) = 0) :
    (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π ((r : ℂ) • firstCoordVec n)) ≤
      ∏ i, ballInd r (π i c0) := by
  by_cases hv : linProj π ((r : ℂ) • firstCoordVec n) ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1
  · rw [Set.indicator_of_mem hv]
    have : ∀ i, ballInd r (π i c0) = 1 := by
      intro i
      have hi := PiLp.norm_apply_le (linProj π ((r : ℂ) • firstCoordVec n)) i
      rw [linProj_smul_firstCoordVec π r c0 hc0 i, norm_mul, Complex.norm_real,
        Real.norm_eq_abs] at hi
      rw [Metric.mem_ball, dist_zero_right] at hv
      simp [ballInd, Set.indicator, show |r| * ‖π i c0‖ < 1 from hi.trans_lt hv]
    simp [this]
  · rw [Set.indicator_of_notMem hv]; exact bot_le
end GroundTheory.Heights₂.Heights.LeadBlockGaussTail
