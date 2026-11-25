-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isPreconnected_punctured_ball_7486948dcaa3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:34:38.025045+00:00
-- url     : https://prove2.me/submissions/4619fa55-6d8a-4ac1-806e-04bf96a8950d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedBranchInOneBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchImageNhdOffCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPuncturedBranchInOneBranch

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
open MvPolynomial ComplexSets Filter Topology
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : ℝ} (hR : 0 < R) :
    IsPreconnected (Metric.ball (0 : ℂ) R \ {0}) := by
  have hH : IsPreconnected {z : ℂ | z.re < Real.log R} := (convex_halfSpace_re_lt _).isPreconnected
  have himage : Complex.exp '' {z : ℂ | z.re < Real.log R} = Metric.ball (0 : ℂ) R \ {0} := by
    ext w
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_sdiff, Metric.mem_ball, dist_zero_right,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, Complex.exp_ne_zero z⟩
      rw [Complex.norm_exp]
      exact (Real.exp_lt_exp.2 hz).trans_eq (Real.exp_log hR)
    · rintro ⟨hw, hw0⟩
      refine ⟨Complex.log w, ?_, Complex.exp_log hw0⟩
      rw [Complex.log_re]
      exact Real.log_lt_log (norm_pos_iff.2 hw0) hw
  rw [← himage]
  exact hH.image _ Complex.continuous_exp.continuousOn
end GroundTheory.Heights₂.Heights
