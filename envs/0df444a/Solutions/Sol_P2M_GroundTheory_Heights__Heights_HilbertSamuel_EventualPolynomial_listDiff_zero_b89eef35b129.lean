-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_zero_b89eef35b129
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:55:26.702433+00:00
-- url     : https://prove2.me/submissions/452af908-9f1d-4ac3-96b6-7d4097306a76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolynomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_cons_912e7bd7a1f6

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Finset fwdDiff
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
variable {K : Type} [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
theorem _root_.solution (L : List K) : listDiff L (0 : (K → ℕ) → ℚ) = 0 := by
  induction L with
  | nil => rfl
  | cons k L ih =>
    funext t
    rw [listDiff_cons, ih]
    simp
end GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
