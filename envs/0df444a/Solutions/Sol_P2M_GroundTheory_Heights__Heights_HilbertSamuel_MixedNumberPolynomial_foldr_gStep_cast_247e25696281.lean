-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_foldr_gStep_cast_247e25696281
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:54.248021+00:00
-- url     : https://prove2.me/submissions/f6154455-cd30-46b4-975b-fcd054a65bad

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
theorem _root_.solution (l : List (K → ℤ)) (h : (K → ℤ) → ℤ) (m : K → ℤ) :
    ((l.foldr gStep h m : ℤ) : ℚ) = l.foldr gStep (fun m => (h m : ℚ)) m := by
  induction l generalizing m with
  | nil => rfl
  | cons b l ih =>
    simp only [List.foldr_cons, gStep]
    push_cast
    rw [ih, ih]
end GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
