-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticePointCount_volume_closedBall_le_45191c17be59
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:02:27.649795+00:00
-- url     : https://prove2.me/submissions/bf8d2738-8ed9-4863-8a59-645d76f2fe3c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VolumeFundamentalDomainEq

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
open MeasureTheory Metric Module Submodule
open scoped ENNReal Pointwise
open GroundTheory.Heights₂.Heights.LatticePointCount
namespace GroundTheory.Heights₂.Heights.LatticePointCount
theorem _root_.solution (r : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    volume (closedBall (0 : EuclideanSpace ℝ (Fin r)) R) ≤ ENNReal.ofReal (2 * R) ^ r := by
  have hmp : MeasurePreserving (@WithLp.ofLp 2 (Fin r → ℝ)) := PiLp.volume_preserving_ofLp (Fin r)
  calc volume (closedBall (0 : EuclideanSpace ℝ (Fin r)) R)
      ≤ volume ((@WithLp.ofLp 2 (Fin r → ℝ)) ⁻¹' closedBall (0 : Fin r → ℝ) R) := by
        apply measure_mono
        intro y hy
        simp only [Set.mem_preimage, mem_closedBall, dist_zero_right] at hy ⊢
        refine (pi_norm_le_iff_of_nonneg hR).2 fun i => ?_
        exact (PiLp.norm_apply_le y i).trans hy
    _ = volume (closedBall (0 : Fin r → ℝ) R) :=
        hmp.measure_preimage measurableSet_closedBall.nullMeasurableSet
    _ = ENNReal.ofReal (2 * R) ^ r := by rw [Real.volume_pi_closedBall _ hR, Fintype.card_fin, ENNReal.ofReal_pow (by positivity)]
end GroundTheory.Heights₂.Heights.LatticePointCount
