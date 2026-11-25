-- Prove2me | solution 1 for P2M_PI_FJMX_leadT_der_rows__f69cea871e0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:01:01.19473+00:00
-- url     : https://prove2.me/submissions/53361c26-4ecb-4d35-b2bf-4869e0af3e3a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
import Theorems.Thm_PI_FJMX_deriv_det_eq_zero_rows


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
    (h : ∀ i₀ : Fin m, i₀.val < t → (∀ j : Fin k, j.val < t → D (M i₀ j) = 0) ∨
      ∃ i₁ : Fin m, i₁.val < t ∧ i₁ ≠ i₀ ∧ ∃ e : A, ∀ j : Fin k, j.val < t → D (M i₀ j) = e * M i₁ j) :
    D (PI.FJM.leadT M t) = 0 := by
  unfold PI.FJM.leadT
  split_ifs with hh
  · apply deriv_det_eq_zero_rows
    intro i
    rcases h (Fin.castLE hh.1 i) (by simp) with h0 | ⟨i₁, hi₁, hne, e, he⟩
    · left
      intro j
      simp only [Matrix.submatrix_apply]
      exact h0 _ (by simp)
    · right
      refine ⟨⟨i₁.val, hi₁⟩, ?_, e, ?_⟩
      · intro hc
        apply hne
        ext
        simp [← hc]
      · intro j
        simp only [Matrix.submatrix_apply]
        rw [he _ (by simp)]
        rfl
  · simp
end PI.FJMX
