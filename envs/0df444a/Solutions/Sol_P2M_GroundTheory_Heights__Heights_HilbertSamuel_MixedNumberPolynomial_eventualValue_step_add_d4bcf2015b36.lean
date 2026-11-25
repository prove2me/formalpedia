-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eventualValue_step_add_d4bcf2015b36
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:58.406398+00:00
-- url     : https://prove2.me/submissions/703c56b8-55d9-4a56-ad1b-06ab5dbe3b7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eventualValue_of_eventually_b6c759acb41a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eventually_sub_ac7cc952d78a

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
theorem _root_.solution (G : (K → ℤ) → ℤ) (x y : K → ℤ)
    (hx : ∃ c, ∀ᶠ m in atTop, gStep x G m = c) (hy : ∃ c, ∀ᶠ m in atTop, gStep y G m = c) :
    eventualValue (gStep (x + y) G) = eventualValue (gStep x G) + eventualValue (gStep y G) := by
  obtain ⟨cx, hcx⟩ := hx
  obtain ⟨cy, hcy⟩ := hy
  rw [eventualValue_of_eventually hcx, eventualValue_of_eventually hcy]
  apply eventualValue_of_eventually
  filter_upwards [hcx, eventually_sub hcy x] with m h1 h2
  rw [← h1, ← h2]
  simp only [gStep]
  rw [show m - x - y = m - (x + y) from sub_sub m x y]
  abel
end GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
