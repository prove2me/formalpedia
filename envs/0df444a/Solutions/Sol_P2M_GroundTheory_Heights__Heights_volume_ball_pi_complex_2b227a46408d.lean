-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_volume_ball_pi_complex_2b227a46408d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:51.501079+00:00
-- url     : https://prove2.me/submissions/e2123619-05f4-4f8d-a42a-204af784e42c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetBallCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSmallSetBallCover

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
open MvPolynomial MeasureTheory ComplexSets Metric
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (c : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    volume (ball c ρ) = ENNReal.ofReal ((Real.pi * ρ ^ 2) ^ n) := by
  rw [ball_pi c hρ, volume_pi_pi]
  simp only [Complex.volume_ball, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hρ.le,
    mul_comm, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
end GroundTheory.Heights₂.Heights
