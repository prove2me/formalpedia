-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_sum_eq_73cf2fba62b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:53:00.361634+00:00
-- url     : https://prove2.me/submissions/97c01020-0696-4afc-aaf6-430d88ef550f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMixedDiffConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
theorem _root_.solution (b : K → ℤ) (p : MvPolynomial K ℚ) :
    shiftPoly b p = ∑ v ∈ p.support, shiftPoly b (monomial v (coeff v p)) ∧
      polyStep b p = ∑ v ∈ p.support, polyStep b (monomial v (coeff v p)) := by
  have hs : shiftPoly b p = ∑ v ∈ p.support, shiftPoly b (monomial v (coeff v p)) := by
    conv_lhs => rw [p.as_sum]
    simp only [shiftPoly, map_sum]
  refine ⟨hs, ?_⟩
  simp only [polyStep, Finset.sum_sub_distrib]
  rw [← hs, ← p.as_sum]
end GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
