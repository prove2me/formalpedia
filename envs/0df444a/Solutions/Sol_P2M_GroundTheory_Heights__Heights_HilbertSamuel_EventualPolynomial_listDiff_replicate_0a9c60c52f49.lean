-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_replicate_0a9c60c52f49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:55:25.389526+00:00
-- url     : https://prove2.me/submissions/57fb4366-4786-43f2-a1ad-d2d71fb49d91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolynomial

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
theorem _root_.solution (j : ℕ) (k : K) (g : (K → ℕ) → ℚ) :
    listDiff (List.replicate j k) g = (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, Function.iterate_succ_apply', ← ih]; rfl
end GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
