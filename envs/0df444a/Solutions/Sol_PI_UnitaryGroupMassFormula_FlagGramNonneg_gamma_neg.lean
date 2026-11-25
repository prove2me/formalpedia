-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.gamma_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:26.554588+00:00
-- url     : https://prove2.me/submissions/76ea397e-d199-4291-91ab-9507bd4d059b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_BinaryFormMulEqNormSqAdd
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_binaryForm_mul_eq_normSq_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_gamma_form

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg
namespace PI.UnitaryGroupMassFormula.FlagGramNonneg
theorem _root_.solution (r : ℕ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (s : ℂ)
    (hs : Complex.normSq s < T * T') (c : Fin r ⊕ Fin 2 → ℂ) (hc : c ≠ 0) :
    (star c ⬝ᵥ (gamma r T T' s *ᵥ c)).re < 0 := by
  rw [gamma_form]
  have hS : 0 ≤ ∑ a, Complex.normSq (c (Sum.inl a)) :=
    Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)
  have hd : 0 < T * T' - Complex.normSq s := by linarith
  have hq : ∀ x y : ℂ,
      0 ≤ T * Complex.normSq x + T' * Complex.normSq y - 2 * (conj x * s * y).re := by
    intro x y
    have h := binaryForm_mul_eq_normSq_add T T' s x y
    have h0 : 0 ≤ Complex.normSq ((T : ℂ) * x - s * y) +
        (T * T' - Complex.normSq s) * Complex.normSq y :=
      add_nonneg (Complex.normSq_nonneg _) (mul_nonneg hd.le (Complex.normSq_nonneg _))
    nlinarith
  have hqpos : ∀ x y : ℂ, (x ≠ 0 ∨ y ≠ 0) →
      0 < T * Complex.normSq x + T' * Complex.normSq y - 2 * (conj x * s * y).re := by
    intro x y hxy
    by_cases hy : y = 0
    · have hx : x ≠ 0 := hxy.resolve_right (not_not.mpr hy)
      have hnx : 0 < Complex.normSq x := Complex.normSq_pos.mpr hx
      subst hy
      simp only [mul_zero, sub_zero, add_zero, Complex.zero_re, Complex.normSq_zero]
      nlinarith [mul_pos hT hnx]
    · have h := binaryForm_mul_eq_normSq_add T T' s x y
      have hny : 0 < Complex.normSq y := Complex.normSq_pos.mpr hy
      have h0 : 0 < Complex.normSq ((T : ℂ) * x - s * y) +
          (T * T' - Complex.normSq s) * Complex.normSq y :=
        add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (mul_pos hd hny)
      nlinarith
  by_cases hin : ∀ a, c (Sum.inl a) = 0
  · have hxy : c (Sum.inr 0) ≠ 0 ∨ c (Sum.inr 1) ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
      simp only [Pi.zero_apply] at hi
      rcases i with a | ⟨_ | _ | k, hk⟩
      · exact absurd (hin a) hi
      · exact Or.inl hi
      · exact Or.inr hi
      · omega
    have := hqpos _ _ hxy
    linarith
  · push_neg at hin
    obtain ⟨a, ha⟩ := hin
    have hpos : 0 < ∑ b, Complex.normSq (c (Sum.inl b)) :=
      Finset.sum_pos' (fun b _ => Complex.normSq_nonneg _)
        ⟨a, Finset.mem_univ _, Complex.normSq_pos.mpr ha⟩
    have := hq (c (Sum.inr 0)) (c (Sum.inr 1))
    linarith
end PI.UnitaryGroupMassFormula.FlagGramNonneg
