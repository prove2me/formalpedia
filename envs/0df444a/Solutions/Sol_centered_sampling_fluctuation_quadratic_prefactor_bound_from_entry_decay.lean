-- Prove2me | solution 1 for centered_sampling_fluctuation_quadratic_prefactor_bound_from_entry_decay
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T18:52:46.737886+00:00
-- url     : https://prove2.me/submissions/03ac8633-40e7-4065-852b-8ab7cfe0092a

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

private theorem spectralNorm_smul {n₁ n₂ : Nat} (c : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (c • X) = |c| * spectralNorm X := by
  unfold spectralNorm
  rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs]

private theorem spectralNorm_nonneg {n₁ n₂ : Nat} (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    0 ≤ spectralNorm X := by
  unfold spectralNorm; exact norm_nonneg _

theorem solution
    (Cfixed : ℝ) :
    0 < Cfixed →
    ∃ Cpref : ℝ, 0 < Cpref ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ → 1 ≤ μ₀ →
        ∀ Centry : ℝ, 0 < Centry →
        ∀ (Omega : Finset (Fin n₁ × Fin n₂)) (X Y : Matrix (Fin n₁) (Fin n₂) ℝ),
        Y = centeredSamplingFluctuation Omega ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X →
        entrySupNorm X ≤ Centry * Real.rpow lam (-1) →
        CenteredSamplingSpectralBound Omega ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
            (Cfixed * Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * entrySupNorm X) →
        spectralNorm Y ≤
          (Cpref * Centry) * Real.rpow lam (-1) *
            Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
  intro hCf
  refine ⟨Cfixed, hCf, ?_⟩
  intro β lam _ _ n₁ n₂ r m μ₀ _ _ _ _ _ Centry _ Omega X Y hY hEB hSB
  unfold CenteredSamplingSpectralBound at hSB
  rw [hY]
  set sb : ℝ := Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) with hsb
  have hnn : 0 ≤ Cfixed * sb := by positivity
  calc spectralNorm (centeredSamplingFluctuation Omega ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ))) X)
      ≤ Cfixed * sb * entrySupNorm X := hSB
    _ ≤ Cfixed * sb * (Centry * Real.rpow lam (-1)) := mul_le_mul_of_nonneg_left hEB hnn
    _ = (Cfixed * Centry) * Real.rpow lam (-1) * sb := by ring
