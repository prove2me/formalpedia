-- Prove2me | solution 1 for centered_sampling_jensen_pointwise_independent_copy_bound_of_sample_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T03:24:37.891162+00:00
-- url     : https://prove2.me/submissions/3e80325a-26a7-480e-9d6c-53a57c669ba6

import Definitions.Def_matrix_completion_rademacher
import Theorems.Thm_bernoulli_powerset_expectation_single_coordinate
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.MeanInequalities

open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1000000

namespace ProveJensen

/-- `spectralNorm` is subadditive (it is an operator norm). -/
theorem spectralNorm_add_le {n1 n2 : ℕ} (A B : RealMatrix n1 n2) :
    spectralNorm (A + B) ≤ spectralNorm A + spectralNorm B := by
  unfold spectralNorm
  rw [show Matrix.toEuclideanLin (A + B)
      = Matrix.toEuclideanLin A + Matrix.toEuclideanLin B from by simp [map_add],
    map_add]
  exact norm_add_le _ _

/-- `spectralNorm` is nonneg. -/
theorem spectralNorm_nonneg {n1 n2 : ℕ} (A : RealMatrix n1 n2) :
    0 ≤ spectralNorm A := norm_nonneg _

/-- `spectralNorm 0 = 0`. -/
theorem spectralNorm_zero {n1 n2 : ℕ} :
    spectralNorm (0 : RealMatrix n1 n2) = 0 := by
  unfold spectralNorm; simp

/-- `spectralNorm` of a nonneg scalar multiple. -/
theorem spectralNorm_smul_nonneg {n1 n2 : ℕ} (c : ℝ) (hc : 0 ≤ c) (A : RealMatrix n1 n2) :
    spectralNorm (c • A) = c * spectralNorm A := by
  unfold spectralNorm
  rw [show Matrix.toEuclideanLin (c • A)
      = c • Matrix.toEuclideanLin A from by simp [map_smul],
    map_smul, norm_smul]
  simp [Real.norm_eq_abs, abs_of_nonneg hc]

/-- spectralNorm of a zero-weighted sum: triangle inequality over a Finset with
nonneg coefficients. -/
theorem spectralNorm_sum_smul_le {n1 n2 : ℕ} {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (A : ι → RealMatrix n1 n2) :
    spectralNorm (∑ i ∈ s, w i • A i) ≤ ∑ i ∈ s, w i * spectralNorm (A i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      rw [show (0 : RealMatrix n1 n2) = (0 : ℝ) • (0 : RealMatrix n1 n2) from by simp,
        spectralNorm_smul_nonneg 0 (le_refl 0)]
      simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hwa : 0 ≤ w a := hw a (Finset.mem_insert_self a s)
    have hws : ∀ i ∈ s, 0 ≤ w i := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    calc spectralNorm (w a • A a + ∑ i ∈ s, w i • A i)
        ≤ spectralNorm (w a • A a) + spectralNorm (∑ i ∈ s, w i • A i) :=
          spectralNorm_add_le _ _
      _ = w a * spectralNorm (A a) + spectralNorm (∑ i ∈ s, w i • A i) := by
          rw [spectralNorm_smul_nonneg _ hwa]
      _ ≤ w a * spectralNorm (A a) + ∑ i ∈ s, w i * spectralNorm (A i) := by
          have := ih hws; linarith

/-- Weights sum to one: `∑_Ω w(Ω) = 1` (witness coordinate `w0` needed for the
single-coordinate identity). -/
theorem weights_sum_one {n1 n2 : ℕ} (p : ℝ) (w0 : Fin n1 × Fin n2) :
    ∑ Omega : Finset (Fin n1 × Fin n2), bernoulliObservationWeight p Omega = 1 := by
  have h := bernoulli_powerset_expectation_single_coordinate (n₁ := n1) (n₂ := n2) p
    w0 (fun _ => (1:ℝ))
  simpa [bernoulliExpectation] using h

/-- Each Bernoulli weight is nonneg for `p ∈ [0,1]`. -/
theorem weight_nonneg {n1 n2 : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n1 × Fin n2)) : 0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  have h1 : (0:ℝ) ≤ 1 - p := by linarith
  positivity

/-- The weighted matrix expectation of `centeredSamplingFluctuation` vanishes. -/
theorem fluct_mean_zero {n1 n2 : ℕ} (p : ℝ) (hp : p ≠ 0) (X : RealMatrix n1 n2) :
    ∑ Omega' : Finset (Fin n1 × Fin n2),
        bernoulliObservationWeight p Omega' • centeredSamplingFluctuation Omega' p X
      = (0 : RealMatrix n1 n2) := by
  funext i j
  -- entrywise:  ∑ w(Ω') · F(Ω')_{ij} = 0
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul]
  -- F(Ω')_{ij} = p⁻¹ * (samplingProjection Ω' X - p • X)_{ij}
  --            = p⁻¹ * ( (if (i,j)∈Ω' then X i j else 0) - p * X i j )
  have hentry : ∀ Omega' : Finset (Fin n1 × Fin n2),
      centeredSamplingFluctuation Omega' p X i j
        = (fun x : ℝ => p⁻¹ * (X i j * (x - p))) (if (i,j) ∈ Omega' then 1 else 0) := by
    intro Omega'
    unfold centeredSamplingFluctuation
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    unfold samplingProjection
    by_cases h : (i,j) ∈ Omega' <;> simp only [h, if_true, if_false] <;> ring
  simp only [hentry]
  rw [← bernoulliExpectation]
  rw [bernoulli_powerset_expectation_single_coordinate p (i,j)
        (fun x => p⁻¹ * (X i j * (x - p)))]
  field_simp
  ring

/-- Power-mean Jensen for `^q`, `q ≥ 1`, over probability weights. -/
theorem power_mean_jensen {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (q : ℕ) (hq : 1 ≤ q)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, w i * x i) ^ q ≤ ∑ i ∈ s, w i * x i ^ q := by
  have hconv : ConvexOn ℝ (Set.Ici (0:ℝ)) (fun t => t ^ (q:ℝ)) :=
    convexOn_rpow (by exact_mod_cast hq)
  have hmem : ∀ i ∈ s, x i ∈ Set.Ici (0:ℝ) := fun i hi => hx i hi
  have hJ := hconv.map_sum_le hw hsum hmem
  simp only [smul_eq_mul] at hJ
  have hL : (∑ i ∈ s, w i * x i) ^ (q:ℝ) = (∑ i ∈ s, w i * x i) ^ q := by
    rw [Real.rpow_natCast]
  have hR : ∀ i ∈ s, w i * x i ^ (q:ℝ) = w i * x i ^ q := by
    intro i hi; rw [Real.rpow_natCast]
  rw [hL] at hJ
  rw [Finset.sum_congr rfl hR] at hJ
  exact hJ

/-- centeredSamplingFluctuation vanishes when `p = 0` (since `0⁻¹ = 0`). -/
theorem fluct_p_zero {n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) :
    centeredSamplingFluctuation Omega 0 X = 0 := by
  unfold centeredSamplingFluctuation
  simp

end ProveJensen

open ProveJensen in
/-- `centered_sampling_jensen_pointwise_independent_copy_bound_of_sample_ratio`.
Pointwise Jensen: `‖F(Ω)‖^q ≤ E_{Ω'}‖F(Ω)−F(Ω')‖^q`, where `F` is the centered
sampling fluctuation at `p = m/(n₁n₂)`.  Proof = (i) `E_{Ω'}[F(Ω')] = 0`
(coordinate-marginal mean-zero), so `E_{Ω'}[F(Ω)−F(Ω')] = F(Ω)`; (ii) Jensen for the
operator norm: `‖E[·]‖ ≤ E‖·‖`; (iii) power-mean Jensen `(E g)^q ≤ E g^q` for `q ≥ 1`.
Source: Candès–Recht 2009/2012, §6.1 (symmetrization preliminary). -/
theorem solution :
    ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
      ∀ Omega : Finset (Fin n₁ × Fin n₂),
        spectralNorm
            (centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q ≤
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega' =>
              spectralNorm
                (centeredSamplingFluctuation Omega
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X -
                  centeredSamplingFluctuation Omega'
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) := by
  intro n₁ n₂ m q X hn₁ hn₂ hm hq Omega
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hn₁R : (0:ℝ) < (n₁:ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0:ℝ) < (n₂:ℝ) := by exact_mod_cast hn₂
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one (by positivity)]
    have : (m:ℝ) ≤ (n₁:ℝ) * (n₂:ℝ) := by exact_mod_cast hm
    linarith
  -- a witness coordinate (n₁,n₂ > 0)
  have hw0 : Fin n₁ × Fin n₂ := (⟨0, hn₁⟩, ⟨0, hn₂⟩)
  -- p = 0 edge:  all fluctuations vanish ⇒ both sides 0.
  rcases eq_or_lt_of_le hp0 with hpeq | hppos
  · -- p = 0:  every fluctuation at p is 0.
    have hp0' : p = 0 := hpeq.symm
    have hfz : ∀ Ω, centeredSamplingFluctuation Ω p X = 0 := by
      intro Ω; rw [hp0']; exact fluct_p_zero Ω X
    rw [hfz Omega, spectralNorm_zero, zero_pow (by omega : q ≠ 0)]
    -- goal: 0 ≤ bernoulliExpectation p (fun Ω' => spectralNorm (0 - F Ω')^q)
    unfold bernoulliExpectation
    apply Finset.sum_nonneg
    intro Omega' _
    exact mul_nonneg (weight_nonneg hp0 hp1 Omega') (pow_nonneg (spectralNorm_nonneg _) q)
  -- main case  0 < p ≤ 1
  have hpne : p ≠ 0 := ne_of_gt hppos
  set F : Finset (Fin n₁ × Fin n₂) → RealMatrix n₁ n₂ :=
    fun Ω => centeredSamplingFluctuation Ω p X with hF
  set g : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Ω' => spectralNorm (F Omega - F Ω') with hg
  have hg_nn : ∀ Ω', 0 ≤ g Ω' := fun Ω' => spectralNorm_nonneg _
  have hweights1 : ∑ Ω' : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω' = 1 :=
    weights_sum_one p hw0
  have hweights_nn : ∀ Ω' ∈ (Finset.univ : Finset (Finset (Fin n₁ × Fin n₂))),
      0 ≤ bernoulliObservationWeight p Ω' := fun Ω' _ => weight_nonneg hp0 hp1 Ω'
  -- STEP 2:  spectralNorm (F Omega) ≤ ∑ w(Ω') g(Ω').
  have hmatsum : ∑ Ω' : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Ω' • (F Omega - F Ω') = F Omega := by
    have hsplit : ∑ Ω' : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Ω' • (F Omega - F Ω')
        = (∑ Ω' : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω') • F Omega
          - ∑ Ω' : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω' • F Ω' := by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro Ω' _; rw [smul_sub]
    rw [hsplit, hweights1, one_smul, hF, fluct_mean_zero p hpne X, sub_zero]
  have hstep2 : spectralNorm (F Omega) ≤
      ∑ Ω' : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω' * g Ω' := by
    calc spectralNorm (F Omega)
        = spectralNorm (∑ Ω' : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p Ω' • (F Omega - F Ω')) := by rw [hmatsum]
      _ ≤ ∑ Ω' : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p Ω' * spectralNorm (F Omega - F Ω') :=
            spectralNorm_sum_smul_le _ _ hweights_nn _
      _ = ∑ Ω' : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω' * g Ω' := rfl
  have hpow : spectralNorm (F Omega) ^ q ≤
      (∑ Ω' : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω' * g Ω') ^ q :=
    pow_le_pow_left₀ (spectralNorm_nonneg _) hstep2 q
  have hjensen : (∑ Ω' : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω' * g Ω') ^ q ≤
      ∑ Ω' : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω' * g Ω' ^ q :=
    power_mean_jensen _ _ _ q hq hweights_nn hweights1 (fun Ω' _ => hg_nn Ω')
  calc spectralNorm (F Omega) ^ q
      ≤ (∑ Ω' : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω' * g Ω') ^ q := hpow
    _ ≤ ∑ Ω' : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω' * g Ω' ^ q := hjensen
    _ = bernoulliExpectation p (fun Ω' => g Ω' ^ q) := by rw [bernoulliExpectation]
