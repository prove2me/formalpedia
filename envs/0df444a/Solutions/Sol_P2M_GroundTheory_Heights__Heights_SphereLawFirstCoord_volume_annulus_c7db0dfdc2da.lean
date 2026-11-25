-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_annulus_c7db0dfdc2da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:16:31.967863+00:00
-- url     : https://prove2.me/submissions/5f9457a1-dd57-4d8b-b435-fb872e52b36a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawFirstCoord

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
open MeasureTheory ProbabilityTheory Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereLawFirstCoord
open SphereMean
namespace GroundTheory.Heights₂.Heights.SphereLawFirstCoord
theorem _root_.solution {a : ℝ} (ha : 0 ≤ a) (s : ℝ) :
    volume {w : ℂ | a ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 < s} = ENNReal.ofReal (s - a) * NNReal.pi := by
  rcases le_or_gt s a with hsa | hsa
  · have : {w : ℂ | a ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 < s} = ∅ := by
      ext w
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro h
      linarith
    rw [this, measure_empty, ENNReal.ofReal_of_nonpos (by linarith), zero_mul]
  · have hset : {w : ℂ | a ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 < s} = Metric.ball 0 √s \ Metric.ball 0 √a := by
      ext w
      simp only [mem_ofPred_eq, mem_sdiff, Metric.mem_ball, dist_zero_right, not_lt]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(Real.lt_sqrt (norm_nonneg w)).2 h2, Real.sqrt_le_iff.2 ⟨norm_nonneg w, h1⟩⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(Real.sqrt_le_iff.1 h2).2, (Real.lt_sqrt (norm_nonneg w)).1 h1⟩
    rw [hset, measure_sdiff (Metric.ball_subset_ball (Real.sqrt_le_sqrt hsa.le))
      measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne, Complex.volume_ball,
      Complex.volume_ball, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (ha.trans hsa.le), Real.sq_sqrt ha,
      ← ENNReal.sub_mul (fun _ _ ↦ ENNReal.coe_ne_top), ENNReal.ofReal_sub _ ha]
end GroundTheory.Heights₂.Heights.SphereLawFirstCoord
