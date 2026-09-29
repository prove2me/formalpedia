-- Prove2me | solution 1 for centered_sampling_fluctuation_linear_neumann_threshold_from_entry_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:49:41.948688+00:00
-- url     : https://prove2.me/submissions/dd69ae45-ec6a-4c1f-a4f9-8d08c88e4b7d

import Theorems.Thm_centered_sampling_fluctuation_linear_neumann_prefactor_bound_from_entry_scale
import Theorems.Thm_linear_neumann_centered_sampling_prefactor_absorbed_by_sample_lower

open MatrixCompletion

/-- Decompose the linear Neumann fixed-matrix threshold into the raw
fixed-matrix event bound and the final scalar sample-lower-bound absorption. -/
theorem solution
    (Cfixed : ℝ) :
    0 < Cfixed →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ Centry : ℝ, 0 < Centry →
        ∀ (Omega : Finset (Fin n₁ × Fin n₂))
          (X Y : Matrix (Fin n₁) (Fin n₂) ℝ),
        Y =
          centeredSamplingFluctuation Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X →
        entrySupNorm X ≤
          Centry * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                    (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm X) →
        spectralNorm Y ≤
          (Cthreshold * Centry) * Real.rpow lam (-1) := by
  intro hCfixed
  rcases centered_sampling_fluctuation_linear_neumann_prefactor_bound_from_entry_scale
      Cfixed hCfixed with
    ⟨Cpref, hCpref, hPref⟩
  rcases linear_neumann_centered_sampling_prefactor_absorbed_by_sample_lower
      Cpref hCpref with
    ⟨Cthreshold, hCthreshold, hAbsorb⟩
  refine ⟨Cthreshold, hCthreshold, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ μ₁ hn₁ hn₂ hr hm hμ₀ hμ₁
    hSample Centry hCentry Omega X Y hY hEntry hEvent
  exact le_trans
    (hPref β hβ n₁ n₂ r m μ₀ μ₁ hn₁ hn₂ hr hm hμ₀ hμ₁
      Centry hCentry Omega X Y hY hEntry hEvent)
    (hAbsorb β lam hβ hlam n₁ n₂ r m μ₀ μ₁ hn₁ hn₂ hr hm hμ₀ hμ₁
      hSample Centry hCentry)
