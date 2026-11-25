-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_monomial_good_f0dadbd829fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:52:49.733793+00:00
-- url     : https://prove2.me/submissions/87d5c0ee-1edc-46d1-9bd3-b7a09869bdb6

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
theorem _root_.solution (b : K → ℤ) (s : K →₀ ℕ) (a : ℚ) :
    (shiftPoly b (monomial s a)).totalDegree ≤ (monomial s a).totalDegree ∧
      (polyStep b (monomial s a) = 0 ∨
        (polyStep b (monomial s a)).totalDegree + 1 ≤ (monomial s a).totalDegree) := by
  refine MvPolynomial.induction_on_monomial (motive := fun q =>
    (shiftPoly b q).totalDegree ≤ q.totalDegree ∧
      (polyStep b q = 0 ∨ (polyStep b q).totalDegree + 1 ≤ q.totalDegree)) ?_ ?_ s a
  · intro a; simp [shiftPoly, polyStep]
  · intro p k hp
    obtain ⟨h1, h2⟩ := hp
    by_cases hp0 : p = 0
    · subst hp0; simp [shiftPoly, polyStep]
    have hdeg : (p * X k).totalDegree = p.totalDegree + 1 := by
      rw [totalDegree_mul_of_isDomain hp0 (X_ne_zero k), totalDegree_X]
    have hXC : (X k - C ((b k : ℤ) : ℚ) : MvPolynomial K ℚ).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (max_le (totalDegree_X k).le (by rw [totalDegree_C]; omega))
    have hsh : shiftPoly b (p * X k) = shiftPoly b p * (X k - C ((b k : ℤ) : ℚ)) := by
      simp [shiftPoly]
    have hst : polyStep b (p * X k) = polyStep b p * X k + C ((b k : ℤ) : ℚ) * shiftPoly b p := by
      rw [polyStep, polyStep, hsh]; ring
    refine ⟨?_, Or.inr ?_⟩
    · rw [hsh, hdeg]
      exact (totalDegree_mul _ _).trans (add_le_add h1 hXC)
    · rw [hst, hdeg, add_le_add_iff_right]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · rcases h2 with h2 | h2
        · rw [h2, zero_mul, totalDegree_zero]; exact zero_le
        · exact (totalDegree_mul _ _).trans (by rw [totalDegree_X]; exact h2)
      · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact h1)
end GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
