-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_mixedDiff_cons_be1bace3a907
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:26:33.145806+00:00
-- url     : https://prove2.me/submissions/a7252f74-cce2-4625-a36b-49de548300f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_mixedDiff_eq_3099f1494d11

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
theorem _root_.solution {n : ℕ} (v : K → ℤ) (t : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) :
    mixedDiff (Fin.cons v t : Fin (n + 1) → K → ℤ) h = gStep v (mixedDiff t h) := by
  simp only [mixedDiff_eq, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.foldr_cons]
end GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
