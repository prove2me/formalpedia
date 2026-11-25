-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_dPoly_monomial_0e1b8897bee7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:16:30.819266+00:00
-- url     : https://prove2.me/submissions/4280004a-2c44-4fdc-b011-be40ae99b93d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_dPoly_mul_ec7023b28eaf

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
theorem _root_.solution (b : K → ℤ) (s : K →₀ ℕ) (a : ℚ) :
    Low (dPoly b (monomial s a)) (monomial s a).totalDegree := by
  refine MvPolynomial.induction_on_monomial
    (motive := fun p => Low (dPoly b p) p.totalDegree) (fun a => ?_) (fun p n ih => ?_) s a
  · exact Or.inl (by simp [dPoly])
  · by_cases hp : p = 0
    · exact Or.inl (by simp [hp, dPoly])
    show Low (dPoly b (p * X n)) (p * X n).totalDegree
    rw [totalDegree_mul_of_isDomain hp (X_ne_zero n), totalDegree_X]
    refine low_dPoly_mul ih (Or.inr ?_) le_rfl (totalDegree_X n).le
    have hXn : dPoly b (X n) = C (b n : ℚ) := by simp [dPoly]
    rw [hXn, totalDegree_C]
    exact Nat.zero_lt_one
end GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
