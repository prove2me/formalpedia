-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VarietyLelongMono_euclBall_measure_a192beebcffd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:22:56.69095+00:00
-- url     : https://prove2.me/submissions/7e9930dd-264e-41b3-9345-71590f1e7038

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyLelongMono

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
open MvPolynomial MeasureTheory
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace VarietyLelongMono
theorem _root_.solution (d : ℕ) (z : EuclideanSpace ℂ (Fin d)) {r : ℝ} (hr : 0 < r) :
    μH[((2 * d : ℕ) : ℝ)] (Metric.ball z r) =
      ENNReal.ofReal (r ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) := by
  have hf : Module.finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin d)), Complex.finrank_real_complex,
      finrank_euclideanSpace_fin]
  have h : ((2 * d : ℕ) : ℝ) = ((Module.finrank ℝ (EuclideanSpace ℂ (Fin d)) : ℕ) : ℝ) := by rw [hf]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hb : ∀ (x : EuclideanSpace ℂ (Fin 0)) (t : ℝ), 0 < t → Metric.ball x t = Set.univ := fun x t ht =>
      Set.eq_univ_of_forall fun y => Metric.mem_ball.2 (by rw [Subsingleton.elim y x, dist_self]; exact ht)
    rw [hb z r hr, hb 0 1 one_pos]
    simp
  · have : Nontrivial (EuclideanSpace ℂ (Fin d)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hf]; omega)
    rw [h, Measure.addHaar_ball _ _ hr.le, hf]
end VarietyLelongMono
end GroundTheory.Heights₂.Heights
