-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_SmallBallVolume_proof_7c05c00ac1b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:57:39.978726+00:00
-- url     : https://prove2.me/submissions/07124f1c-af39-4404-9ca9-84cbdc8f75cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSmallBallVolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_pi_pow_div_factorial_le_six_36070f0ce513
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_pi_pow_mul_two_pow_div_doubleFactorial_le_six_35886cc5d309

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Real Module
open scoped Nat
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace SmallBallVolume
theorem _root_.solution : SmallBallVolume.Statement := by
  intro R
  unfold unitBallVolume
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin R)) = R := finrank_euclideanSpace_fin
  rcases Nat.even_or_odd' R with ⟨k, hk | hk⟩
  · rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      simp only [mul_zero] at hk
      subst hk
      have : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1)).toReal ≤ 1 := by
        have hle : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1) ≤ 1 := by
          calc volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1)
              ≤ volume (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) := measure_mono (Set.subset_univ _)
            _ = 1 := by
              rw [← (PiLp.volume_preserving_toLp (Fin 0)).measure_preimage
                MeasurableSet.univ.nullMeasurableSet, Set.preimage_univ, MeasureTheory.volume_pi,
                Measure.pi_univ]
              simp
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle)
      linarith
    · have : Nontrivial (EuclideanSpace ℝ (Fin R)) :=
        Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
      rw [InnerProductSpace.volume_ball_of_dim_even (hfin.trans hk), ENNReal.ofReal_one, one_pow,
        one_mul, ENNReal.toReal_ofReal (by positivity)]
      exact pi_pow_div_factorial_le_six k
  · rw [InnerProductSpace.volume_ball_of_dim_odd (hfin.trans hk), ENNReal.ofReal_one, one_pow,
      one_mul, ENNReal.toReal_ofReal (by positivity), hfin, hk]
    exact pi_pow_mul_two_pow_div_doubleFactorial_le_six k
end SmallBallVolume
end GroundTheory.Heights₂.Heights.HilbertSamuel
