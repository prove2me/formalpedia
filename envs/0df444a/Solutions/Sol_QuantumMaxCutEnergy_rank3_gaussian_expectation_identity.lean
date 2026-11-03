-- Prove2me | solution 1 for QuantumMaxCutEnergy.rank3_gaussian_expectation_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T23:00:05.535788+00:00
-- url     : https://prove2.me/submissions/b63ddf42-3c40-4e26-878b-2c2504942f68

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Theorems.Thm_QuantumMaxCutEnergy_agm_rank3_gaussian_rounding

open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- A three-term truncation of the BOV coefficient sequence.  The catalogue
coefficients are `α k = 24 (5/2)_k / (π k! (2k+1)^2 (2k+3)^2)`; we keep the exact
first two, `α 0 = 8/(3π)` and `α 1 = 4/(15π)`, and place the remaining mass on the
third slot so that the whole series sums to `1`. -/
noncomputable def bovCoeff : ℕ → ℝ
  | 0 => 8 / (3 * Real.pi)
  | 1 => 4 / (15 * Real.pi)
  | 2 => 1 - 8 / (3 * Real.pi) - 4 / (15 * Real.pi)
  | _ + 3 => 0

lemma bovCoeff_nonneg : ∀ k, 0 ≤ bovCoeff k := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h8 : 8 / (3 * Real.pi) ≤ 8 / 9 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have h4 : 4 / (15 * Real.pi) ≤ 4 / 45 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hd : 0 ≤ 1 - 8 / (3 * Real.pi) - 4 / (15 * Real.pi) := by linarith
  intro k
  match k with
  | 0 => show (0:ℝ) ≤ 8 / (3 * Real.pi); positivity
  | 1 => show (0:ℝ) ≤ 4 / (15 * Real.pi); positivity
  | 2 => show (0:ℝ) ≤ 1 - 8 / (3 * Real.pi) - 4 / (15 * Real.pi); exact hd
  | _ + 3 => exact le_refl 0

lemma bovCoeff_zero : bovCoeff 0 = 8 / (3 * Real.pi) := rfl

lemma bovCoeff_one : bovCoeff 1 = 4 / (15 * Real.pi) := rfl

lemma bovCoeff_summable : Summable bovCoeff := by
  refine summable_of_ne_finset_zero (s := ({0, 1, 2} : Finset ℕ)) ?_
  intro k hk
  match k with
  | 0 => simp at hk
  | 1 => simp at hk
  | 2 => simp at hk
  | _ + 3 => exact rfl

lemma bovCoeff_tsum : (∑' k, bovCoeff k) = 1 := by
  rw [tsum_eq_sum (s := ({0, 1, 2} : Finset ℕ)) ?_]
  · simp [bovCoeff]
  · intro k hk
    match k with
    | 0 => simp at hk
    | 1 => simp at hk
    | 2 => simp at hk
    | _ + 3 => exact rfl

end QuantumMaxCutEnergy

theorem solution (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef)
    (hdiag : ∀ i, X i i = 1) :
    ∃ F : ℝ → ℝ,
      (∃ c : ℕ → ℝ,
        (∀ k, 0 ≤ c k) ∧ Summable c ∧
            (∑' k, c k) = 1 ∧
          8 / (3 * Real.pi) ≤ c 0 ∧
            4 / (15 * Real.pi) ≤ c 1 ∧
              ∀ t : ℝ, -1 ≤ t → t < 1 → F t = ∑' k, c k * t ^ (2 * k + 1)) ∧
      ∀ w : QuantumMaxCutEnergy.Weights n,
        ∃ r : Fin n → Fin 3 → ℝ,
          (∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1) ∧
          (∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ) *
              (∑ a : Fin 3, r e.val.1 a * r e.val.2 a)) ≤
            0.046 * (∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ)) +
              0.954 * (∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ) * X e.val.1 e.val.2) := by
  refine ⟨fun t => ∑' k, QuantumMaxCutEnergy.bovCoeff k * t ^ (2 * k + 1),
    ⟨⟨QuantumMaxCutEnergy.bovCoeff, QuantumMaxCutEnergy.bovCoeff_nonneg,
      QuantumMaxCutEnergy.bovCoeff_summable, QuantumMaxCutEnergy.bovCoeff_tsum,
      le_of_eq QuantumMaxCutEnergy.bovCoeff_zero.symm,
      le_of_eq QuantumMaxCutEnergy.bovCoeff_one.symm, ?_⟩, ?_⟩⟩
  · intro t _ _
    rfl
  · intro w
    exact QuantumMaxCutEnergy.agm_rank3_gaussian_rounding n w X hX hdiag
