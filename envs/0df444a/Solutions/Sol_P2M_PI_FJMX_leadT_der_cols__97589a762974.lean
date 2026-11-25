-- Prove2me | solution 1 for P2M_PI_FJMX_leadT_der_cols__97589a762974
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:55:35.6871+00:00
-- url     : https://prove2.me/submissions/5e46fe52-b331-4dfb-b3fb-130d33147d5e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
import Theorems.Thm_PI_FJMX_deriv_det_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMX
variable {A : Type*} [CommRing A] [Algebra ℂ A] {m k : ℕ}
namespace PI.FJMX
theorem _root_.solution (D : Derivation ℂ A A) (M : Matrix (Fin m) (Fin k) A) (t : ℕ)
    (h : ∀ j₀ : Fin k, j₀.val < t → (∀ i : Fin m, i.val < t → D (M i j₀) = 0) ∨
      ∃ j₁ : Fin k, j₁.val < t ∧ j₁ ≠ j₀ ∧ ∃ e : A, ∀ i : Fin m, i.val < t → D (M i j₀) = e * M i j₁) :
    D (PI.FJM.leadT M t) = 0 := by
  unfold PI.FJM.leadT
  split_ifs with hh
  · apply deriv_det_eq_zero
    intro j
    rcases h (Fin.castLE hh.2 j) (by simp) with h0 | ⟨j₁, hj₁, hne, e, he⟩
    · left
      intro i
      simp only [Matrix.submatrix_apply]
      exact h0 _ (by simp)
    · right
      refine ⟨⟨j₁.val, hj₁⟩, ?_, e, ?_⟩
      · intro hc
        apply hne
        ext
        simp [← hc]
      · intro i
        simp only [Matrix.submatrix_apply]
        rw [he _ (by simp)]
        rfl
  · simp
end PI.FJMX
