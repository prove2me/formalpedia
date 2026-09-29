-- Prove2me | solution 1 for candes_romberg_talagrand_finite_bernoulli_coordinate_process_bad_event_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-30T03:01:18.918592+00:00
-- url     : https://prove2.me/submissions/e4bebef8-7ee0-4a44-ba13-9f549a9fc6e3

import Theorems.Thm_candes_romberg_talagrand_finite_bool_product_coordinate_process_bad_event_log_tail
import Theorems.Thm_candes_romberg_bad_event_powerset_from_bool_product_coordinate_process

open MatrixCompletion
open scoped Classical BigOperators

theorem solution :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n₁ n₂ m : ℕ) (ι : Type) [Fintype ι] [Nonempty ι]
        (coeff : ι → Fin n₁ → Fin n₂ → ℝ) (B sigmaSq t : ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
          |coeff a i j| ≤ B) →
        (∀ a : ι,
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (coeff a i j) ^ 2 ≤ sigmaSq) →
        let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
        let process : ι → Finset (Fin n₁ × Fin n₂) → ℝ :=
          fun a Omega =>
            ∑ i : Fin n₁, ∑ j : Fin n₂,
              (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
                coeff a i j)
        let Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
          fun Omega =>
            Finset.univ.sup' Finset.univ_nonempty (fun a : ι => process a Omega)
        let Zbar : Finset (Fin n₁ × Fin n₂) → ℝ :=
          fun Omega =>
            Finset.univ.sup' Finset.univ_nonempty
              (fun a : ι => |process a Omega|)
        bernoulliEventProb p
            (fun Omega => ¬ |Z Omega - bernoulliExpectation p Z| ≤ t) ≤
          3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq + B * bernoulliExpectation p Zbar))) := by
  exact candes_romberg_bad_event_powerset_from_bool_product_coordinate_process
    candes_romberg_talagrand_finite_bool_product_coordinate_process_bad_event_log_tail
