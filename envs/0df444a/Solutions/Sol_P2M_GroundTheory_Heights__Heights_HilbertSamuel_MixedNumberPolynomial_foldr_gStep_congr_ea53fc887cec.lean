-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_foldr_gStep_congr_ea53fc887cec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:26:28.602252+00:00
-- url     : https://prove2.me/submissions/b485fb5c-bfbd-4a50-bdfc-c0ece6c8ab88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
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
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
theorem _root_.solution {G : Type*} [AddCommGroup G] (l : List (K → ℤ)) {h h' : (K → ℤ) → G}
    (hh : ∀ᶠ m in atTop, h m = h' m) :
    ∀ᶠ m in atTop, l.foldr gStep h m = l.foldr gStep h' m := by
  induction l with
  | nil => simpa using hh
  | cons b l ih =>
    filter_upwards [ih, eventually_sub ih b] with m h1 h2
    simp only [List.foldr_cons, gStep, h1, h2]
end GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
