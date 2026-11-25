-- Prove2me | solution 1 for PI.FJMB.diagonal_image_block_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:30.941557+00:00
-- url     : https://prove2.me/submissions/e2e3cb22-29ed-49f3-9732-85d035c62982

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurCauchy
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_DiagonalImageBlockFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}
namespace PI.FJMB
theorem _root_.solution : HypFree := by
  intro σ m n ι hι P
  have hC : ∀ c : ℂ, ∀ e ∈ (MvPolynomial.C c : MvPolynomial σ ℂ).support, ∀ x, e (ι x) = 0 := by
    intro c e he x
    rw [MvPolynomial.C_apply] at he
    have h0 := MvPolynomial.support_monomial_subset he
    rw [Finset.mem_singleton] at h0
    rw [h0]
    rfl
  have hadd : ∀ Q R : MvPolynomial σ ℂ, (∀ e ∈ Q.support, ∀ x, e (ι x) = 0) →
      (∀ e ∈ R.support, ∀ x, e (ι x) = 0) → ∀ e ∈ (Q + R).support, ∀ x, e (ι x) = 0 := by
    intro Q R hQ hR e he x
    rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
    · exact hQ e h x
    · exact hR e h x
  have hmul : ∀ Q R : MvPolynomial σ ℂ, (∀ e ∈ Q.support, ∀ x, e (ι x) = 0) →
      (∀ e ∈ R.support, ∀ x, e (ι x) = 0) → ∀ e ∈ (Q * R).support, ∀ x, e (ι x) = 0 := by
    intro Q R hQ hR e he x
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul Q R he)
    rw [Finsupp.add_apply, hQ a ha x, hR b hb x]
  have hgen : ∀ w, ∀ e ∈ (diagOne' ι w).support, ∀ x, e (ι x) = 0 := by
    intro w
    unfold diagOne'
    split_ifs with h1 h2
    · simpa using hC 0
    · simpa using hC 1
    · intro e he x
      have hne : w ≠ ι x := by
        rintro rfl
        obtain ⟨i, k⟩ := x
        by_cases hik : (i : ℕ) = k
        · exact h2 ⟨i, k, rfl, hik⟩
        · exact h1 ⟨i, k, rfl, hik⟩
      rw [MvPolynomial.support_X, Finset.mem_singleton] at he
      rw [he, Finsupp.single_apply, if_neg hne]
  induction P using MvPolynomial.induction_on
  next a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    exact hC a
  next p q hp hq =>
    rw [map_add]
    exact hadd _ _ hp hq
  next p w hp =>
    rw [map_mul, MvPolynomial.aeval_X]
    exact hmul _ _ hp (hgen w)
end PI.FJMB
