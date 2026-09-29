-- Prove2me | solution 1 for centered_sampling_coefficient_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T21:08:13.167551+00:00
-- url     : https://prove2.me/submissions/281db4ed-2bba-45f3-9cbb-4bc049af6d92

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_bernoulli_powerset_expectation_double
import Theorems.Thm_bernoulli_powerset_expectation_single_coordinate
import Theorems.Thm_bernoulli_powerset_expectation_pair_coordinate
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1600000

private theorem coeff_eq_linear {n₁ n₂ : ℕ}
    (p : ℝ) (B : Matrix (Fin n₁) (Fin n₂) ℝ)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    matrixEntrySum (centeredSamplingFluctuation Omega p B) =
      ∑ w : Fin n₁ × Fin n₂, (p⁻¹ * (B w.1 w.2) * ((if w ∈ Omega then 1 else 0) - p)) := by
  classical
  unfold matrixEntrySum centeredSamplingFluctuation
  apply Finset.sum_congr rfl
  intro w _
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  unfold samplingProjection
  by_cases h : (w.1, w.2) ∈ Omega
  · simp only [h, if_true]; ring
  · simp only [h, if_false]; ring

/-- `centered_sampling_coefficient_second_moment`.

**Exact second moment (variance) of the scalar centered sampling coefficient.**
For `Coeff Ω = matrixEntrySum (centeredSamplingFluctuation Ω p B)
= ∑_{ij} p⁻¹(𝟙[(i,j)∈Ω]−p) B_{ij}` and `p ≠ 0`,
$$\mathbb{E}[\mathrm{Coeff}^2] = \frac{1-p}{p}\,\|B\|_F^2.$$
Proof: write `Coeff = ∑_w h_w(𝟙[w∈Ω])` with `h_w(x)=p⁻¹B_w(x−p)`, square via
`Fintype.sum_mul_sum` to a double sum, push the expectation through both sums
(double-linearity), and evaluate each `(w,w')` term: the diagonal `w=w'` is the
single-coordinate second moment `p·h_w(1)²+(1-p)·h_w(0)² = ((1-p)/p)B_w²`; every
off-diagonal `w≠w'` term factorizes (pair independence) into a product of two
single-coordinate means, each of which is zero (the centered terms have mean 0).
Only the diagonal survives, summing to `((1-p)/p)·∑_w B_w² = ((1-p)/p)‖B‖_F²`.
This is the variance `σ²` input (with `(1-p)/p ≤ 1/p` for `p∈(0,1]`) to the
q-moment Bernstein estimate. -/
theorem solution {n₁ n₂ : ℕ} (p : ℝ) (hp : p ≠ 0)
    (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    bernoulliExpectation p
      (fun Omega => (matrixEntrySum (centeredSamplingFluctuation Omega p B)) ^ 2) =
      ((1 - p) / p) * frobeniusNormSq B := by
  classical
  set hfun : (Fin n₁ × Fin n₂) → ℝ → ℝ :=
    fun w x => p⁻¹ * (B w.1 w.2) * (x - p) with hhfun
  have hsq : (fun Omega : Finset (Fin n₁ × Fin n₂) =>
        (matrixEntrySum (centeredSamplingFluctuation Omega p B)) ^ 2) =
      (fun Omega => ∑ w : Fin n₁ × Fin n₂, ∑ w' : Fin n₁ × Fin n₂,
        hfun w (if w ∈ Omega then 1 else 0) * hfun w' (if w' ∈ Omega then 1 else 0)) := by
    funext Omega
    rw [coeff_eq_linear p B Omega, sq, Fintype.sum_mul_sum]
  rw [hsq]
  rw [bernoulli_powerset_expectation_double p (fun w w' x y => hfun w x * hfun w' y)]
  have heval : ∀ w w' : Fin n₁ × Fin n₂,
      bernoulliExpectation p
        (fun Omega => hfun w (if w ∈ Omega then 1 else 0) *
          hfun w' (if w' ∈ Omega then 1 else 0)) =
      (if w = w' then ((1 - p) / p) * (B w.1 w.2)^2 else 0) := by
    intro w w'
    by_cases hww : w = w'
    · subst hww
      simp only [if_true]
      have := bernoulli_powerset_expectation_single_coordinate (n₁ := n₁) (n₂ := n₂) p w
        (fun x => hfun w x * hfun w x)
      rw [this]
      simp only [hhfun]
      have hpp : p⁻¹ * p = 1 := inv_mul_cancel₀ hp
      field_simp
      ring
    · simp only [hww, if_false]
      have := bernoulli_powerset_expectation_pair_coordinate (n₁ := n₁) (n₂ := n₂) p w w' hww
        (hfun w) (hfun w')
      rw [this]
      simp only [hhfun]
      have hpp : p⁻¹ * p = 1 := inv_mul_cancel₀ hp
      have hz1 : p * (p⁻¹ * (B w.1 w.2) * (1 - p)) +
          (1 - p) * (p⁻¹ * (B w.1 w.2) * (0 - p)) = 0 := by
        field_simp; ring
      rw [hz1]; ring
  rw [Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun w' _ => heval w w'))]
  have hdiag : ∀ w : Fin n₁ × Fin n₂,
      (∑ w' : Fin n₁ × Fin n₂, (if w = w' then ((1 - p) / p) * (B w.1 w.2)^2 else 0)) =
        ((1 - p) / p) * (B w.1 w.2)^2 := by
    intro w
    rw [Finset.sum_eq_single w]
    · simp
    · intro b _ hb; rw [if_neg (fun he => hb he.symm)]
    · intro hb; exact absurd (Finset.mem_univ w) hb
  rw [Finset.sum_congr rfl (fun w _ => hdiag w), ← Finset.mul_sum]
  congr 1
  unfold frobeniusNormSq
  rw [Fintype.sum_prod_type]
