-- Prove2me | solution 1 for SuttonBartoRL.OffPolicy.pbe_gradient_factors
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T18:26:34.383622+00:00
-- url     : https://prove2.me/submissions/443bf9d4-6ce3-4812-9360-89e72198d567

import Mathlib
import Definitions.Def_SuttonBartoRL_OffPolicy_LinearGeometry

open Matrix SuttonBartoRL.OffPolicy

section PB
variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

theorem bρ (π b : SuttonBartoRL.FiniteMDP.Policy S A)
    (hcov : ∀ s a, 0 < π.prob s a → 0 < b.prob s a) (s : S) (a : A) :
    b.prob s a * isRatio π b s a = π.prob s a := by
  unfold isRatio
  by_cases hb0 : b.prob s a = 0
  · have : π.prob s a = 0 := by
      rcases (π.nonneg s a).lt_or_eq with h | h
      · have := hcov s a h; rw [hb0] at this; exact absurd this (lt_irrefl 0)
      · exact h.symm
    rw [hb0, this]; simp
  · field_simp

theorem bρ_sum (M : MDP S A) (π b : SuttonBartoRL.FiniteMDP.Policy S A)
    (hcov : ∀ s a, 0 < π.prob s a → 0 < b.prob s a) (s : S) (F : S → ℝ → ℝ) :
    ∑ a, b.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * (isRatio π b s a * F s' r) =
      ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * F s' r := by
  apply Finset.sum_congr rfl; intro a _
  rw [← bρ π b hcov s a, mul_assoc]
  congr 1
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s' _
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _
  ring

theorem psum1 (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) (c : ℝ) :
    ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * c = c := by
  have : ∀ a, ∑ s', ∑ r ∈ M.R, M.p s a s' r * c = c := by
    intro a
    simp_rw [← Finset.sum_mul]; rw [M.p_sum s a, one_mul]
  simp_rw [this]; rw [← Finset.sum_mul, π.sum_one, one_mul]
theorem sum3_mul (M : MDP S A) (s : S) (f : A → ℝ) (h : A → S → ℝ → ℝ) (c : ℝ) :
    ∑ a, f a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * (h a s' r * c) =
      (∑ a, f a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * h a s' r) * c := by
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
theorem pX (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) (F : S → ℝ) :
    ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * F s' = ∑ s', policyTrans M π s s' * F s' := by
  unfold policyTrans MDP.trans
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s' _
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro r _
  ring
end PB

theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : MDP S A) (π b : SuttonBartoRL.FiniteMDP.Policy S A) (hcov : ∀ s a, 0 < π.prob s a → 0 < b.prob s a)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (μ : S → ℝ) (hμ0 : ∀ s, 0 ≤ μ s) (hμ1 : ∑ s, μ s = 1)
    (X : Matrix S (Fin d) ℝ) (w : Fin d → ℝ) :
    (Xᵀ *ᵥ (Dmat μ *ᵥ bellmanError M π γ X w) = ∑ s, (μ s * bellmanError M π γ X w s) • X s ∧
      ∑ s, (μ s * bellmanError M π γ X w s) • X s
        = behaviorExp M b μ
            (fun s a s' r => (isRatio π b s a * (r + γ * (w ⬝ᵥ X s') - w ⬝ᵥ X s)) • X s)) ∧
    behaviorExp M b μ (fun s a s' _ => isRatio π b s a • vecMulVec (γ • X s' - X s) (X s))
      = (γ • (policyTrans M π * X) - X)ᵀ * Dmat μ * X ∧
    (Xᵀ * Dmat μ * X = ∑ s, μ s • vecMulVec (X s) (X s) ∧
      ∑ s, μ s • vecMulVec (X s) (X s) = behaviorExp M b μ (fun s _ _ _ => vecMulVec (X s) (X s))) := by
  have hv : ∀ s', w ⬝ᵥ X s' = vw X w s' := fun s' => by
    unfold vw; rw [dotProduct_comm]; rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · ext i
    simp only [Dmat, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec,
      dotProduct, transpose_apply]
    apply Finset.sum_congr rfl; intro s _
    simp [diagonal_apply]; ring
  · ext i
    simp only [behaviorExp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl; intro s _
    have key : ∑ a, b.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r *
        (isRatio π b s a * ((r + γ * (w ⬝ᵥ X s') - w ⬝ᵥ X s) * X s i)) =
        bellmanError M π γ X w s * X s i := by
      rw [bρ_sum M π b hcov s (fun s' r => (r + γ * (w ⬝ᵥ X s') - w ⬝ᵥ X s) * X s i)]
      rw [sum3_mul]
      congr 1
      simp only [hv]
      unfold bellmanError bellmanOp
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      rw [psum1]
    rw [mul_assoc, ← key]
    congr 1
    apply Finset.sum_congr rfl; intro a _
    congr 1
    apply Finset.sum_congr rfl; intro s' _
    apply Finset.sum_congr rfl; intro r _
    ring
  · ext i j
    simp only [behaviorExp, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply,
      Pi.sub_apply, Pi.smul_apply, mul_apply, transpose_apply, Dmat, diagonal_apply, Matrix.sub_apply]
    apply Finset.sum_congr rfl; intro s _
    rw [bρ_sum M π b hcov s (fun s' r => (γ * X s' i - X s i) * X s j), sum3_mul M s (π.prob s)
      (fun _ s' _ => γ * X s' i - X s i) (X s j)]
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [psum1]
    have h1 : ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * (γ * X s' i) =
        γ * ∑ s', policyTrans M π s s' * X s' i := by
      rw [pX M π s (fun s' => γ * X s' i), Finset.mul_sum]
      apply Finset.sum_congr rfl; intro s' _; ring
    rw [h1]
    simp [ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq]
    ring
  · ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, mul_apply,
      transpose_apply, Dmat, diagonal_apply]
    apply Finset.sum_congr rfl; intro s _
    simp [ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq]
    ring
  · ext i j
    simp only [behaviorExp, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]
    apply Finset.sum_congr rfl; intro s _
    rw [psum1 M b s]
