-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_exists_max_c79fae73757f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:35.761512+00:00
-- url     : https://prove2.me/submissions/d63008e6-65ec-41b0-be88-4c6decd02294

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong

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
open MvPolynomial MeasureTheory ProbabilityTheory Real
noncomputable section
open GroundTheory.Heights₂.Heights.PointwiseLelong
variable {N : ℕ}
namespace GroundTheory.Heights₂.Heights.PointwiseLelong
theorem _root_.solution (hN : 1 ≤ N) (Q : MvPolynomial (Fin N) ℂ) :
    ∃ p : Fin N → ℂ, ∑ j, ‖p j‖ ^ 2 = 1 ∧
      ∀ z : Fin N → ℂ, ∑ j, ‖z j‖ ^ 2 = 1 → ‖eval z Q‖ ≤ ‖eval p Q‖ := by
  let S := {z : Fin N → ℂ | ∑ j, ‖z j‖ ^ 2 = 1}
  have hcont : Continuous fun z : Fin N → ℂ => ∑ j, ‖z j‖ ^ 2 := by fun_prop
  have hcl : IsClosed S := isClosed_eq hcont continuous_const
  have hb : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin N → ℂ)) (r := 1)).subset fun z hz => ?_
    have hz' : ∑ j, ‖z j‖ ^ 2 = 1 := hz
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    have hj : ‖z j‖ ^ 2 ≤ 1 := by
      rw [← hz']
      exact Finset.single_le_sum (f := fun i => ‖z i‖ ^ 2) (fun i _ => sq_nonneg ‖z i‖)
        (Finset.mem_univ j)
    nlinarith [norm_nonneg (z j)]
  have hne : S.Nonempty := by
    refine ⟨Pi.single ⟨0, hN⟩ 1, ?_⟩
    show ∑ j, ‖(Pi.single ⟨0, hN⟩ (1 : ℂ) : Fin N → ℂ) j‖ ^ 2 = 1
    rw [Finset.sum_eq_single ⟨0, hN⟩ (fun j _ hj => by simp [hj]) (by simp)]
    simp
  obtain ⟨p, hpS, hmax⟩ := (Metric.isCompact_of_isClosed_isBounded hcl hb).exists_isMaxOn hne
    (continuous_norm.comp (MvPolynomial.continuous_eval Q)).continuousOn
  exact ⟨p, hpS, fun z hz => isMaxOn_iff.mp hmax z hz⟩
end GroundTheory.Heights₂.Heights.PointwiseLelong
