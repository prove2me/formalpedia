-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_dPoly_mul_ec7023b28eaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:31:55.834191+00:00
-- url     : https://prove2.me/submissions/879a16d1-b5be-49e0-8dd4-1742795ae052

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_add_ba467e24cca8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_mul_right_578929c5d444
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_mul_left_63399e4aa36e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_dPoly_mul_b634b238dade
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_totalDegree_sub_dPoly_le_cff9bd5d1b19

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
variable {K : Type*}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
theorem _root_.solution {b : K → ℤ} {A B : MvPolynomial K ℚ} {α β : ℕ}
    (hA : Low (dPoly b A) α) (hB : Low (dPoly b B) β) (hdA : A.totalDegree ≤ α)
    (hdB : B.totalDegree ≤ β) : Low (dPoly b (A * B)) (α + β) := by
  rw [dPoly_mul]
  exact low_add (low_mul_right hA hdB) (low_mul_left hB (totalDegree_sub_dPoly_le hdA hA))
end GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
