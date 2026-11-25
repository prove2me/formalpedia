-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_mixedDiff_zero_4b76ed212846
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:44:35.329814+00:00
-- url     : https://prove2.me/submissions/7ed7abe8-23d7-40f4-bb35-1602d34db083

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {K : Type*} {n : ℕ} (bs : Fin n → K → ℤ) :
    mixedDiff bs (0 : (K → ℤ) → ℤ) = 0 := by
  unfold mixedDiff
  induction List.ofFn bs with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldr_cons, ih]
    funext m
    simp [diffStep]
end GroundTheory.Heights₂.Heights.NumbersDVR
