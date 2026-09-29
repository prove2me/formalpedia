-- Prove2me | solution 1 for Polynomial.exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/913330d9-df87-5780-a544-09659d3f1fa8

import Mathlib
import Theorems.Thm_Polynomial_shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence
import Theorems.Thm_Polynomial_exists_polynomial_forall_tsum_mul_zpow_eq_of_shellRecurrent_finsum_line
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence

set_option autoImplicit false

theorem solution
    (A : ℤ × ℤ → ℂ) (b : ℤ → ℂ) (α β : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hA : ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
      (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
      (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
        ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
          D₁.coeff i * D₂.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0))
    (hb : ∃ (N₂ : ℤ) (E : Polynomial ℂ) (M' : ℕ), E.eval 0 ≠ 0 ∧
      (∀ m : ℤ, m < N₂ → b m = 0) ∧
      (∀ m : ℕ, M' ≤ m →
        ∑ i ∈ Finset.range (E.natDegree + 1), E.coeff i * b (N₂ + (m : ℤ) - (i : ℤ)) = 0)) :
    ∃ (P Q : Polynomial ℂ) (m₀ : ℤ), Q ≠ 0 ∧
      ∀ X : ℂ, X ≠ 0 →
        Summable (fun n : ℤ × ℤ =>
          A n * b n.1 * α ^ n.1 * β ^ n.2 * X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2)) →
        (∑' n : ℤ × ℤ, A n * b n.1 * α ^ n.1 * β ^ n.2 * X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2)) * Q.eval X =
          X ^ m₀ * P.eval X := by
  obtain ⟨N₁, D₁, D₂, M, hD₁, hD₂, hsupp, hrec⟩ := hA
  have hc := Polynomial.shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence A b α β hα hβ e₁ e₂
    he₁ he₂ ⟨N₁, D₁, D₂, M, hD₁, hD₂, hsupp, hrec⟩ hb
  have hw : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) →
      (fun n : ℤ × ℤ => A n * b n.1 * α ^ n.1 * β ^ n.2) n = 0 := by
    intro n hn
    simp only [hsupp n hn, zero_mul]
  obtain ⟨P, Q, m₀, hQ, h⟩ :=
    Polynomial.exists_polynomial_forall_tsum_mul_zpow_eq_of_shellRecurrent_finsum_line
      (fun n : ℤ × ℤ => A n * b n.1 * α ^ n.1 * β ^ n.2) N₁ hw e₁ e₂ he₁ he₂ hc
  exact ⟨P, Q, m₀, hQ, fun X hX hs => h X hX hs⟩

end S_Polynomial_exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence
end P2MW
export P2MW.S_Polynomial_exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence (solution)
