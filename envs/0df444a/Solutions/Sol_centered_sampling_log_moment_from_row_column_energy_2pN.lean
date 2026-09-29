-- Prove2me | solution 1 for centered_sampling_log_moment_from_row_column_energy_2pN
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-25T09:35:44.250435+00:00
-- url     : https://prove2.me/submissions/945ca251-0a64-48b7-bd84-2d9bd8c6f1b8

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_rademacher
import Theorems.Thm_centered_sampling_symmetrization_moment_bound_of_sample_ratio
import Theorems.Thm_rademacher_pointwise_khintchine_spectral_energy
import Theorems.Thm_bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio
import Theorems.Thm_centered_sampling_log_moment_khintchine_scale_from_symmetrization_and_rademacher
import Theorems.Thm_conditional_khintchine_scale_moment_from_row_column_energy_moment_2pN
import Theorems.Thm_centered_sampling_log_moment_beta_scale_from_khintchine_scale

open MatrixCompletion

/-- `_2pN` Section 6.1 noncommutative-Khintchine conversion: from the supplied
row/column energy log-moment estimate (Lemma 6.2, in the `q ≤ 2pN` window) to the
spectral log-moment bound for the centered sampling fluctuation
`p⁻¹(P_Ω − pI)X`.

Assembly of the Section 6.1 chain:
* symmetrization `bExp[‖S‖^q] ≤ Csym^q · bExp[Eε‖S_sym‖^q]`;
* pointwise conditional Khintchine `Eε‖S_sym‖^q ≤ (Ckh·√q·p⁻¹·√maxEnergy)^q`
  (Tropp even-`2n` Schatten variance scale + dilation + spectral≤Schatten + window);
* monotone lift to the Bernoulli expectation;
* the energy power-mean step converting `bExp[(Ckh·√q·p⁻¹·√maxEnergy)^q]` into
  `(Crad·√(qN/p)·‖X‖_∞)^q`;
* the symmetrization/Khintchine combiner giving `(Cq·√(qN/p)·‖X‖_∞)^q`;
* the `β`-scale absorption `√(qN/p) → √(βN log N/p)` using `q ≤ 2β log N`. -/
theorem solution
    (Cenergy : ℝ) :
    0 < Cenergy →
    ∃ Cmoment : ℝ, 0 < Cmoment ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        (∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) ∧
          (q : ℝ) ≤ 2 * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂))) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                (max (sampledRowEnergyMax Omega X)
                  (sampledColumnEnergyMax Omega X)) ^ q) ≤
            (Cenergy * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q) →
        ∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                spectralNorm
                  (centeredSamplingFluctuation Omega
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
            (Cmoment * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm X) ^ q := by
  intro hCenergy
  -- Global constants from the four reusable bricks.
  obtain ⟨Csym, hCsym, hSymmBound⟩ :=
    centered_sampling_symmetrization_moment_bound_of_sample_ratio
  obtain ⟨Ckh, hCkh, hPointwise⟩ := rademacher_pointwise_khintchine_spectral_energy
  obtain ⟨Crad, hCrad, hEnergyToScale⟩ :=
    conditional_khintchine_scale_moment_from_row_column_energy_moment_2pN
      Cenergy Ckh hCenergy hCkh
  obtain ⟨Cq, hCq, hCombine⟩ :=
    centered_sampling_log_moment_khintchine_scale_from_symmetrization_and_rademacher
      Csym Crad hCsym hCrad
  obtain ⟨Cmoment, hCmoment, hBetaScale⟩ :=
    centered_sampling_log_moment_beta_scale_from_khintchine_scale Cq hCq
  refine ⟨Cmoment, hCmoment, ?_⟩
  intro β hβ n₁ n₂ m X hn₁ hn₂ hm hmLower hEnergyExists
  obtain ⟨q, hq1, hqLower, hqUpper, hqSample2, hEnergyBound⟩ := hEnergyExists
  refine ⟨q, hq1, hqLower, ?_⟩
  -- (1) Lift the pointwise Khintchine bound to the Bernoulli expectation.
  have hRadBExp :
      bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            rademacherExpectation
              (fun eps =>
                spectralNorm
                  (rademacherSampledMatrix Omega eps
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            (Ckh * Real.sqrt (q : ℝ) *
              (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
              Real.sqrt
                (max (sampledRowEnergyMax Omega X)
                  (sampledColumnEnergyMax Omega X))) ^ q) := by
    refine bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio
      Ckh n₁ n₂ m q X hn₁ hn₂ hm ?_
    intro Omega
    exact hPointwise β hβ n₁ n₂ m q X Omega hn₁ hn₂ hq1 hqLower
  -- (2) Energy power-mean: convert the scale-moment into √(qN/p)·‖X‖_∞.
  have hScaleMoment :
      bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            (Ckh * Real.sqrt (q : ℝ) *
              (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
              Real.sqrt
                (max (sampledRowEnergyMax Omega X)
                  (sampledColumnEnergyMax Omega X))) ^ q) ≤
        (Crad * Real.sqrt
          (((q : ℝ) * (↑(max n₁ n₂))) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          entrySupNorm X) ^ q := by
    exact hEnergyToScale β hβ n₁ n₂ m q X hn₁ hn₂ hm hmLower hq1 hqLower hqUpper
      hqSample2 hEnergyBound
  -- (3) Chain pointwise→bExp with energy power-mean to get the Rademacher khintchine scale.
  have hRadScale :
      bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            rademacherExpectation
              (fun eps =>
                spectralNorm
                  (rademacherSampledMatrix Omega eps
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
        (Crad * Real.sqrt
          (((q : ℝ) * (↑(max n₁ n₂))) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          entrySupNorm X) ^ q :=
    le_trans hRadBExp hScaleMoment
  -- (4) Symmetrization bound for the combiner.
  have hSymm := hSymmBound n₁ n₂ m q X hn₁ hn₂ hm hq1
  -- (5) Combiner: bExp[‖S‖^q] ≤ (Cq·√(qN/p)·‖X‖_∞)^q.
  have hKhScale := hCombine n₁ n₂ m q X hq1 hSymm hRadScale
  -- (6) β-scale absorption.
  exact hBetaScale β hβ n₁ n₂ m q X hn₁ hn₂ hm hmLower hq1 hqLower hqUpper hKhScale
