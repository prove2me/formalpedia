-- Prove2me | solution 1 for bernoulli_energy_moment_from_count_moment_and_pointwise_domination
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T22:53:04.648415+00:00
-- url     : https://prove2.me/submissions/6ac36a86-1cb0-483c-9d93-47b83e81d71d

import Definitions.Def_matrix_completion_sampled_counts
open MatrixCompletion

private theorem bow_nonneg {n₁ n₂ : Nat} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Om : Finset (Fin n₁ × Fin n₂)) : 0 ≤ bernoulliObservationWeight p Om := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

theorem solution
    (Ccount : ℝ) :
    0 < Ccount →
    ∃ Cenergy : ℝ, 0 < Cenergy ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (↑(max n₁ n₂)) →
        ∀ (Energy Count : Finset (Fin n₁ × Fin n₂) → ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂), 0 ≤ Energy Omega) →
        (∀ Omega : Finset (Fin n₁ × Fin n₂), 0 ≤ Count Omega) →
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Energy Omega ≤ entrySupNorm X ^ 2 * Count Omega) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega : Finset (Fin n₁ × Fin n₂) => Count Omega ^ q) ≤
          (Ccount * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂))) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega : Finset (Fin n₁ × Fin n₂) => Energy Omega ^ q) ≤
          (Cenergy * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q := by
  intro hCc
  refine ⟨Ccount, hCc, ?_⟩
  intro β hβ n₁ n₂ m q X hn1 hn2 hm hq hqlog hqub Energy Count hEnn hCnn hdom hCmom
  have hden : (0:ℝ) < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one hden]; exact_mod_cast hm
  have hesn : (0:ℝ) ≤ (entrySupNorm X ^ 2) ^ q := by positivity
  calc bernoulliExpectation p (fun Omega => Energy Omega ^ q)
      ≤ bernoulliExpectation p (fun Omega => (entrySupNorm X ^ 2) ^ q * Count Omega ^ q) := by
        unfold bernoulliExpectation
        apply Finset.sum_le_sum
        intro Om _
        have hpt : Energy Om ^ q ≤ (entrySupNorm X ^ 2) ^ q * Count Om ^ q := by
          calc Energy Om ^ q ≤ (entrySupNorm X ^ 2 * Count Om) ^ q :=
                pow_le_pow_left₀ (hEnn Om) (hdom Om) q
            _ = (entrySupNorm X ^ 2) ^ q * Count Om ^ q := mul_pow _ _ _
        exact mul_le_mul_of_nonneg_left hpt (bow_nonneg hp0 hp1 Om)
    _ = (entrySupNorm X ^ 2) ^ q * bernoulliExpectation p (fun Omega => Count Omega ^ q) := by
        unfold bernoulliExpectation
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro Om _; ring
    _ ≤ (entrySupNorm X ^ 2) ^ q * (Ccount * p * (↑(max n₁ n₂))) ^ q :=
        mul_le_mul_of_nonneg_left hCmom hesn
    _ = (Ccount * p * (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q := by
        rw [← mul_pow]; congr 1; ring
