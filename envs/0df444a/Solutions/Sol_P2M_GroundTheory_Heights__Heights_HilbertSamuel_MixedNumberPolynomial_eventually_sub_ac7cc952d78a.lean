-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eventually_sub_ac7cc952d78a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:40.334804+00:00
-- url     : https://prove2.me/submissions/040d34da-28e4-4ef7-a8fb-46bc091a0f3e

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
theorem _root_.solution {P : (K → ℤ) → Prop} (h : ∀ᶠ m in atTop, P m) (x : K → ℤ) :
    ∀ᶠ m in atTop, P (m - x) := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 h
  exact Filter.eventually_atTop.2 ⟨a + x, fun m hm => ha _ (le_sub_iff_add_le.2 hm)⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
