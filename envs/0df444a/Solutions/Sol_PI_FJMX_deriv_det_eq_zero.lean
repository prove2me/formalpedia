-- Prove2me | solution 1 for PI.FJMX.deriv_det_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:47:37.947916+00:00
-- url     : https://prove2.me/submissions/c9ee1b9c-d3df-4222-bb0a-364ceb565f00

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Theorems.Thm_PI_FJMX_deriv_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.FJMX
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
namespace PI.FJMX
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (D : Derivation R A A)
    (M : Matrix n n A)
    (h : ∀ i, (∀ k, D (M k i) = 0) ∨ ∃ i', i' ≠ i ∧ ∃ c : A, ∀ k, D (M k i) = c * M k i') :
    D M.det = 0 := by
  rw [deriv_det]
  apply Finset.sum_eq_zero
  intro i _
  rcases h i with h0 | ⟨i', hne, c, hc⟩
  · have : (fun k => D (M k i)) = 0 := funext h0
    rw [this]
    simpa using Matrix.det_updateCol_smul M i (0 : A) 0
  · have : (fun k => D (M k i)) = c • (fun k => M k i') := funext fun k => by simp [hc k]
    rw [this, Matrix.det_updateCol_smul]
    rw [Matrix.det_zero_of_column_eq hne.symm]
    · simp
    · intro k
      simp [Matrix.updateCol_self, Matrix.updateCol_ne hne]
end PI.FJMX
