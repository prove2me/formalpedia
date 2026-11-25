-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eval_dPoly_efb5ec89d6a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:56:25.417014+00:00
-- url     : https://prove2.me/submissions/819d3391-bbd0-4933-8e36-cd8ac64c5555

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
theorem _root_.solution (b : K → ℤ) (p : MvPolynomial K ℚ) (m : K → ℤ) :
    eval (fun k => (m k : ℚ)) (dPoly b p) =
      eval (fun k => (m k : ℚ)) p - eval (fun k => ((m - b) k : ℚ)) p := by
  show aeval (fun k => (m k : ℚ)) (dPoly b p) =
    aeval (fun k => (m k : ℚ)) p - aeval (fun k => ((m - b) k : ℚ)) p
  have hx : (fun i => aeval (fun k => (m k : ℚ)) (X i - C (b i : ℚ))) =
      fun k => ((m - b) k : ℚ) := by
    funext k
    simp
  rw [dPoly, map_sub, aeval_bind₁, hx]
end GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
