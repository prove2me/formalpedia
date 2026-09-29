-- Prove2me | solution 1 for centered_sampling_coefficient_symmetric_l4_l2_hypercontractivity
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T05:22:35.382855+00:00
-- url     : https://prove2.me/submissions/a6eec465-cf24-4324-9345-b0d0a6237ded

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_centered_sampling_coefficient_fourth_moment
import Theorems.Thm_centered_sampling_coefficient_second_moment
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1600000

/-- **Order-2 (degree-1) L⁴↔L² hypercontractivity at the symmetric rate `p = 1/2`.**
`E[Coeff⁴] ≤ 3 (E[Coeff²])²`, dimension-free. Reduction onto the exact fourth-moment
(`centered_sampling_coefficient_fourth_moment`) and exact second-moment
(`centered_sampling_coefficient_second_moment`) closed forms. At `p = 1/2` the exact
identity is `E[Coeff⁴] = 3 (E[Coeff²])² − 2 ∑_w B_w⁴ ≤ 3 (E[Coeff²])²`. -/
theorem solution {n₁ n₂ : ℕ} (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    bernoulliExpectation (1/2 : ℝ)
      (fun Omega => (matrixEntrySum (centeredSamplingFluctuation Omega (1/2) B)) ^ 4) ≤
      3 * (bernoulliExpectation (1/2 : ℝ)
            (fun Omega => (matrixEntrySum (centeredSamplingFluctuation Omega (1/2) B)) ^ 2)) ^ 2 := by
  classical
  have hp : (1/2 : ℝ) ≠ 0 := by norm_num
  rw [centered_sampling_coefficient_fourth_moment (1/2) hp B,
      centered_sampling_coefficient_second_moment (1/2) hp B]
  -- At p = 1/2: ((1-p)/p) = 1, so E[Coeff²] = frobeniusNormSq B.
  -- The diagonal 4th-moment term simplifies: each per-w term = B_w⁴.
  -- The cross term: μ₂(w) = ((1-p)/p) B_w² = B_w².
  -- Goal becomes:  ∑_w B_w⁴ + 3 ∑_{a≠b} B_a² B_b²  ≤  3 (frobeniusNormSq B)².
  -- Use frobeniusNormSq B = ∑_w B_w² (over the product index).
  have hF : frobeniusNormSq B = ∑ w : Fin n₁ × Fin n₂, (B w.1 w.2)^2 := by
    rw [Fintype.sum_prod_type]; rfl
  -- Simplify the diagonal term per-w to B_w⁴.
  have hdiag : ∀ w : Fin n₁ × Fin n₂,
      ((1/2 : ℝ) * ((1/2 : ℝ)⁻¹ * (B w.1 w.2) * (1 - 1/2))^4
        + (1 - 1/2) * ((1/2 : ℝ)⁻¹ * (B w.1 w.2) * (0 - 1/2))^4)
      = (B w.1 w.2)^4 := by
    intro w; ring
  rw [Finset.sum_congr rfl (fun w _ => hdiag w)]
  -- Simplify the cross-term factors to B²·B².
  have hcross : ∀ a b : Fin n₁ × Fin n₂,
      (if a = b then (0:ℝ) else
        (((1 - 1/2) / (1/2)) * (B a.1 a.2)^2) * (((1 - 1/2) / (1/2)) * (B b.1 b.2)^2))
      = (if a = b then (0:ℝ) else (B a.1 a.2)^2 * (B b.1 b.2)^2) := by
    intro a b; by_cases h : a = b
    · simp [h]
    · simp only [h, if_false]; ring
  rw [Finset.sum_congr rfl (fun a _ =>
        Finset.sum_congr rfl (fun b _ => hcross a b))]
  -- Now: ∑_w B_w⁴ + 3 ∑_a ∑_b [a≠b] B_a² B_b²  ≤  3 ((1-1/2)/(1/2) · frobeniusNormSq B)².
  -- ((1-1/2)/(1/2)) = 1.
  have hone : ((1 - 1/2 : ℝ) / (1/2)) = 1 := by norm_num
  rw [hone, one_mul, hF]
  -- Let S = ∑_w B_w².  Need ∑_w (B_w²)² + 3 ∑_{a≠b} B_a² B_b² ≤ 3 S².
  -- Note S² = ∑_a ∑_b B_a² B_b² = ∑_w (B_w²)² + ∑_{a≠b} B_a² B_b².
  set f : Fin n₁ × Fin n₂ → ℝ := fun w => (B w.1 w.2)^2 with hf
  have hSsq : (∑ w, f w) ^ 2 = (∑ a, ∑ b, f a * f b) := by
    rw [sq, Finset.sum_mul_sum]
  -- Split the full double sum into diagonal + off-diagonal.
  have hsplit : (∑ a, ∑ b, f a * f b)
      = (∑ w, f w * f w) + (∑ a, ∑ b, (if a = b then (0:ℝ) else f a * f b)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a _
    rw [show (f a * f a) = ∑ b, (if a = b then f a * f b else (0:ℝ)) by
          rw [Finset.sum_ite_eq Finset.univ a (fun b => f a * f b)]; simp]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro b _
    by_cases h : a = b
    · simp [h]
    · simp [h]
  -- The diagonal sum equals ∑_w (B_w²)² (= ∑_w f w * f w).
  have hdiagf : (∑ w : Fin n₁ × Fin n₂, (B w.1 w.2)^4) = ∑ w, f w * f w := by
    apply Finset.sum_congr rfl; intro w _; simp only [hf]; ring
  -- The cross sum in the goal matches the off-diagonal sum of f.
  have hcrossf : (∑ a : Fin n₁ × Fin n₂, ∑ b : Fin n₁ × Fin n₂,
        (if a = b then (0:ℝ) else (B a.1 a.2)^2 * (B b.1 b.2)^2))
      = (∑ a, ∑ b, (if a = b then (0:ℝ) else f a * f b)) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    by_cases h : a = b
    · simp [h]
    · simp only [h, if_false, hf]
  rw [hdiagf, hcrossf]
  -- Goal:  (∑ w, f w * f w) + 3 * (∑_{a≠b} f a f b)  ≤  3 * (∑ w, f w)²
  -- i.e.   D + 3 OFF ≤ 3 (D + OFF) = 3D + 3 OFF, i.e. D ≤ 3D, i.e. 0 ≤ 2D.
  set D := (∑ w, f w * f w) with hD
  set OFF := (∑ a, ∑ b, (if a = b then (0:ℝ) else f a * f b)) with hOFF
  have hSsq2 : (∑ w, f w) ^ 2 = D + OFF := by rw [hSsq, hsplit]
  rw [hSsq2]
  have hDnn : 0 ≤ D := by
    rw [hD]; apply Finset.sum_nonneg; intro w _
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith
