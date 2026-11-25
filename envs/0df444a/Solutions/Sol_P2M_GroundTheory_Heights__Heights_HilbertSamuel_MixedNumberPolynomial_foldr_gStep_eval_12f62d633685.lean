-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_foldr_gStep_eval_12f62d633685
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:31:53.653683+00:00
-- url     : https://prove2.me/submissions/22aa6a90-3d97-4b1a-a322-e2217092f3f0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eval_dPoly_efb5ec89d6a8

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
theorem _root_.solution (l : List (K → ℤ)) (p : MvPolynomial K ℚ) (m : K → ℤ) :
    l.foldr gStep (fun m : K → ℤ => eval (fun k => (m k : ℚ)) p) m =
      eval (fun k => (m k : ℚ)) (l.foldr dPoly p) := by
  induction l generalizing m with
  | nil => rfl
  | cons b l ih =>
    simp only [List.foldr_cons, gStep, ih, eval_dPoly]
end GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
