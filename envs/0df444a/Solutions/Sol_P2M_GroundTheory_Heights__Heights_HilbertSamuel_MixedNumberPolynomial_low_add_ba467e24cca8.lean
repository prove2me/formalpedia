-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_add_ba467e24cca8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:40.807977+00:00
-- url     : https://prove2.me/submissions/6e782530-186f-40ff-b074-34653d733c6c

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
theorem _root_.solution {A B : MvPolynomial K ℚ} {N : ℕ} (hA : Low A N) (hB : Low B N) :
    Low (A + B) N := by
  rcases hA with hA | hA
  · simpa [hA] using hB
  rcases hB with hB | hB
  · rw [hB, add_zero]
    exact Or.inr hA
  exact Or.inr ((totalDegree_add A B).trans_lt (max_lt hA hB))
end GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
