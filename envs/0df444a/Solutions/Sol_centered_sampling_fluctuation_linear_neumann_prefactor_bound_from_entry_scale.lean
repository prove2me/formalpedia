-- Prove2me | solution 1 for centered_sampling_fluctuation_linear_neumann_prefactor_bound_from_entry_scale
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T18:48:55.748786+00:00
-- url     : https://prove2.me/submissions/42d851f7-512e-4cdf-bd5d-b0f1fa987fcd

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    (Cfixed : ℝ) :
    0 < Cfixed →
    ∃ Cpref : ℝ, 0 < Cpref ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
        ∀ Centry : ℝ, 0 < Centry →
        let entryScale : ℝ :=
          Centry * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                    (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ))
        ∀ (Omega : Finset (Fin n₁ × Fin n₂))
          (X Y : Matrix (Fin n₁) (Fin n₂) ℝ),
        Y = centeredSamplingFluctuation Omega p X →
        entrySupNorm X ≤ entryScale →
        CenteredSamplingSpectralBound Omega
            p X
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                p) *
              entrySupNorm X) →
        spectralNorm Y ≤
          Cpref * entryScale *
            Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                p) := by
  intro hCf
  refine ⟨Cfixed, hCf, ?_⟩
  intro β _ n₁ n₂ r m μ₀ μ₁ _ _ _ _ _ _ p Centry _ entryScale Omega X Y hY hEB hSB
  unfold CenteredSamplingSpectralBound at hSB
  rw [hY]
  set sb : ℝ := Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) with hsb
  have hnn : 0 ≤ Cfixed * sb := by positivity
  calc spectralNorm (centeredSamplingFluctuation Omega p X)
      ≤ Cfixed * sb * entrySupNorm X := hSB
    _ ≤ Cfixed * sb * entryScale := by
        apply mul_le_mul_of_nonneg_left hEB hnn
    _ = Cfixed * entryScale * sb := by ring
