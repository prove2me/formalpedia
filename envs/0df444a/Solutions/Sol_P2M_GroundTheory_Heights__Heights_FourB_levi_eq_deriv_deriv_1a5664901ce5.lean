-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_levi_eq_deriv_deriv_1a5664901ce5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:05:18.727748+00:00
-- url     : https://prove2.me/submissions/bdc0faab-4b85-4548-a202-a0152b5d7c2b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_fderiv_fderiv_apply_eq_deriv_deriv_cfe20d6f28b7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm Filter Topology Polynomial
noncomputable section
variable {ι : Type*} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution {φ : (ι → ℂ) → ℝ} (hφ : ContDiffAt ℝ 2 φ 0) (w : ι → ℂ) :
    levi φ 0 w = (deriv (deriv fun t : ℝ => φ (t • w)) 0 +
      deriv (deriv fun t : ℝ => φ (t • (Complex.I • w))) 0) / 4 := by
  simp only [levi, fderiv_fderiv_apply_eq_deriv_deriv hφ]
end GroundTheory.Heights₂.Heights.FourB
