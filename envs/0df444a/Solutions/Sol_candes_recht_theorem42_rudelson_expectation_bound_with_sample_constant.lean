-- Prove2me | solution 1 for candes_recht_theorem42_rudelson_expectation_bound_with_sample_constant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T03:13:16.20979+00:00
-- url     : https://prove2.me/submissions/9f94f14c-3a3c-4410-ac86-a0ba8d20618c

import Theorems.Thm_tangent_coordinate_frobenius_bound_from_a0_min_dim
import Theorems.Thm_tangent_coordinate_frobenius_sq_bound_implies_radius_bound
import Theorems.Thm_rudelson_selection_expected_tangent_deviation_from_coordinate_radius_bound_dense_proviso
import Theorems.Thm_rudelson_selection_density_bound_from_a0_dense_sample_bound
import Theorems.Thm_rudelson_min_dim_coordinate_radius_raw_scale_le_one_under_sample_constant
import Theorems.Thm_rudelson_min_dim_coordinate_radius_scale_le_expected_deviation_scale_under_density
import Theorems.Thm_tangent_expected_deviation_core_scale_le_beta_scale
import Theorems.Thm_neumann_remainder_tangent_scale_le_half_from_sample_bound
import Mathlib.Tactic

open MatrixCompletion

/-!
Source: Candes--Recht, PDF pp. 18--19, Theorem 4.2 equation (4.9), including
the proviso that the right-hand side is smaller than `1`.

This reduction proves the expectation bound with smallness from:
* the A0 coordinate Frobenius estimate (equation (4.8));
* the corrected Rudelson selection theorem with explicit raw-scale proviso;
* scalar bridges converting the Candes--Recht sample lower bound into the
  Rudelson lower bound, the raw-scale proviso, and finally `E Z ≤ 1`.
-/
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → A0 S μ₀ →
        (m : ℝ) ≥
          C' * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
            tangentSamplingDeviationScale C β μ₀ (max n₁ n₂) r m ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤ 1 := by
  rcases tangent_coordinate_frobenius_bound_from_a0_min_dim with
    ⟨Ccoord, hCcoord, hCoord⟩
  rcases rudelson_selection_expected_tangent_deviation_from_coordinate_radius_bound_dense_proviso with
    ⟨Csel, hCsel, hSelection⟩
  rcases rudelson_min_dim_coordinate_radius_scale_le_expected_deviation_scale_under_density
      Csel Ccoord hCsel hCcoord with
    ⟨Ccore, hCcore, hCoreScale⟩
  rcases tangent_expected_deviation_core_scale_le_beta_scale Ccore hCcore with
    ⟨Cbeta, hCbeta, hBetaScale⟩
  rcases neumann_remainder_tangent_scale_le_half_from_sample_bound Cbeta with
    ⟨Csmall, hCsmall, hSmall⟩
  rcases rudelson_min_dim_coordinate_radius_raw_scale_le_one_under_sample_constant
      Ccoord hCcoord with
    ⟨Craw, hCraw, hRawScale⟩
  let C : ℝ := max (max (max Cbeta Craw) Csmall) 1
  have hC_pos : 0 < C :=
    lt_of_lt_of_le hCbeta
      (le_trans (le_trans (le_max_left Cbeta Craw) (le_max_left _ Csmall))
        (le_max_left _ 1))
  refine ⟨C, hC_pos, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ S hn₁ hn₂ hr hm hμ₀ hA0 hmLower
  let n : ℕ := max n₁ n₂
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let radiusSq : ℝ := Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))
  let R : ℝ := Real.sqrt radiusSq
  have hCbeta_le_C : Cbeta ≤ C := by
    exact le_trans (le_trans (le_max_left Cbeta Craw) (le_max_left _ Csmall))
      (le_max_left _ 1)
  have hCraw_le_C' : Craw ≤ C' := by
    exact le_trans
      (le_trans (le_trans (le_max_right Cbeta Craw) (le_max_left _ Csmall))
        (le_max_left _ 1)) hC'
  have hCsmall_le_C' : Csmall ≤ C' := by
    exact le_trans (le_trans (le_max_right (max Cbeta Craw) Csmall)
      (le_max_left _ 1)) hC'
  have hOne_le_C' : (1 : ℝ) ≤ C' := by
    exact le_trans (le_max_right (max (max Cbeta Craw) Csmall) 1) hC'
  have hn : 0 < n := by
    dsimp [n]
    exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hn_real_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have hμ₀_nonneg : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hβ_nonneg : 0 ≤ β :=
    le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 2) hβ)
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg hn_real_ge_one
  have hbase_nonneg :
      0 ≤ μ₀ * (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ)) := by
    positivity
  have hmDenseA0 :
      (m : ℝ) ≥ β * μ₀ * (n : ℝ) * (r : ℝ) * Real.log (n : ℝ) := by
    have hle :
        (1 : ℝ) * (μ₀ * (n : ℝ) * (r : ℝ) *
            (β * Real.log (n : ℝ))) ≤
          C' * (μ₀ * (n : ℝ) * (r : ℝ) *
            (β * Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hOne_le_C' hbase_nonneg
    calc
      β * μ₀ * (n : ℝ) * (r : ℝ) * Real.log (n : ℝ)
          = (1 : ℝ) * (μ₀ * (n : ℝ) * (r : ℝ) *
              (β * Real.log (n : ℝ))) := by ring
      _ ≤ C' * (μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ))) := hle
      _ = C' * μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ)) := by ring
      _ ≤ (m : ℝ) := by
        simpa [n, C, mul_assoc] using hmLower
  have hSelectionDense :
      (m : ℝ) ≥ β * (n : ℝ) * (r : ℝ) * Real.log (n : ℝ) :=
    rudelson_selection_density_bound_from_a0_dense_sample_bound
      β μ₀ n r m hβ hn hr hμ₀ hmDenseA0
  have hRadiusSqNonneg : 0 ≤ radiusSq := by
    dsimp [radiusSq]
    positivity
  have hCoordSq :
      TangentCoordinateFrobeniusBound S radiusSq := by
    simpa [radiusSq] using
      hCoord n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
  have hRadius :
      ∀ i : Fin n₁, ∀ j : Fin n₂,
        frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ≤ R := by
    simpa [R] using
      tangent_coordinate_frobenius_sq_bound_implies_radius_bound
        S radiusSq hRadiusSqNonneg hCoordSq
  have hRaw :
      Real.sqrt
          (Real.log (↑(max n₁ n₂)) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * R ≤ 1 := by
    simpa [R, radiusSq, n] using
      hRawScale C' hCraw_le_C' β hβ n₁ n₂ r m μ₀
        hn₁ hn₂ hr hm hμ₀ hmLower
  have hSelectionBound :
      bernoulliExpectation p
          (fun Omega => tangentSamplingDeviation Omega S p) ≤
        Csel *
          Real.sqrt
            (Real.log (↑(max n₁ n₂)) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          R := by
    simpa [p, R] using
      hSelection β hβ n₁ n₂ r m M S R
        hn₁ hn₂ hr hm (Real.sqrt_nonneg radiusSq)
        (by simpa [n] using hSelectionDense) hRaw hRadius
  have hCoreBound :
      bernoulliExpectation p
          (fun Omega => tangentSamplingDeviation Omega S p) ≤
        tangentSamplingExpectedDeviationScale Ccore μ₀ n r m := by
    have hScaleBound :=
      hCoreScale β hβ n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀
        (by simpa [n] using hmDenseA0)
    exact le_trans hSelectionBound (by simpa [p, R, radiusSq, n] using hScaleBound)
  have hBetaBound :
      bernoulliExpectation p
          (fun Omega => tangentSamplingDeviation Omega S p) ≤
        tangentSamplingDeviationScale Cbeta β μ₀ n r m :=
    le_trans hCoreBound (hBetaScale β μ₀ n r m hβ)
  have hScaleMono :
      tangentSamplingDeviationScale Cbeta β μ₀ n r m ≤
        tangentSamplingDeviationScale C β μ₀ n r m := by
    dsimp [tangentSamplingDeviationScale]
    exact mul_le_mul_of_nonneg_right hCbeta_le_C (Real.sqrt_nonneg _)
  have hConclusionScale :
      bernoulliExpectation p
          (fun Omega => tangentSamplingDeviation Omega S p) ≤
        tangentSamplingDeviationScale C β μ₀ n r m :=
    le_trans hBetaBound hScaleMono
  have hSmallLower :
      (m : ℝ) ≥ Csmall * μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ)) := by
    have hle :
        Csmall * (μ₀ * (n : ℝ) * (r : ℝ) *
            (β * Real.log (n : ℝ))) ≤
          C' * (μ₀ * (n : ℝ) * (r : ℝ) *
            (β * Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hCsmall_le_C' hbase_nonneg
    calc
      Csmall * μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ))
          = Csmall * (μ₀ * (n : ℝ) * (r : ℝ) *
              (β * Real.log (n : ℝ))) := by ring
      _ ≤ C' * (μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ))) := hle
      _ = C' * μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ)) := by ring
      _ ≤ (m : ℝ) := by
        simpa [n, C, mul_assoc] using hmLower
  have hSmallScale :
      tangentSamplingDeviationScale Cbeta β μ₀ n r m ≤ (1 : ℝ) / 2 :=
    hSmall β hβ n r m μ₀ hn hr hμ₀ hSmallLower
  have hExpectationSmall :
      bernoulliExpectation p
          (fun Omega => tangentSamplingDeviation Omega S p) ≤ 1 := by
    linarith [hBetaBound, hSmallScale]
  exact ⟨by simpa [p, n] using hConclusionScale,
    by simpa [p] using hExpectationSmall⟩
