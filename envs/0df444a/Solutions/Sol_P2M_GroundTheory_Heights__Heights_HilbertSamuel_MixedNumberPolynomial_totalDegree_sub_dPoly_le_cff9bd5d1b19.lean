-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_totalDegree_sub_dPoly_le_cff9bd5d1b19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:56:27.083826+00:00
-- url     : https://prove2.me/submissions/03a59868-9f72-423a-93c0-ce7c2e2a4cb2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial

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
theorem _root_.solution {b : K → ℤ} {A : MvPolynomial K ℚ} {N : ℕ}
    (hd : A.totalDegree ≤ N) (hl : Low (dPoly b A) N) : (A - dPoly b A).totalDegree ≤ N := by
  refine (totalDegree_sub _ _).trans (max_le hd ?_)
  rcases hl with hl | hl
  · simp [hl]
  · exact hl.le
end GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
