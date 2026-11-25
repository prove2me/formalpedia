-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eventualValue_of_eventually_b6c759acb41a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:44.808391+00:00
-- url     : https://prove2.me/submissions/2193cd5b-5736-46a4-a3ec-aa60109c4f7c

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
variable [DecidableEq K]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
theorem _root_.solution {f : (K → ℤ) → ℤ} {c : ℤ} (h : ∀ᶠ m in atTop, f m = c) :
    eventualValue f = c := by
  have hex : ∃ c, ∀ᶠ m in atTop, f m = c := ⟨c, h⟩
  unfold eventualValue
  rw [dif_pos hex]
  obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and h).exists
  exact hm1.symm.trans hm2
end GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
