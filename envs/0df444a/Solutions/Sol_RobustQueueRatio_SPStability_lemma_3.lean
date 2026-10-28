-- Prove2me | solution 1 for RobustQueueRatio.SPStability.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:00:07.306224+00:00
-- url     : https://prove2.me/submissions/8e8654cd-611f-4b28-9183-dad96fb146ac

import Mathlib
import Definitions.Def_RobustQueueRatio_SPStability_Network
import Definitions.Def_RobustQueueRatio_SPStability_ChenS
import Definitions.Def_RobustQueueRatio_SPStability_RatioMatrix

open Matrix

namespace RQRLemma3Aux

open RobustQueueRatio.SPStability

/-- If two `K × J` matrices agree outside column `k`, the determinant of `G * Δ` is affine
along the segment joining them. -/
theorem det_mul_comb_of_col {J K : ℕ} (G : Matrix (Fin J) (Fin K) ℝ)
    (Δ₁ Δ₂ : Matrix (Fin K) (Fin J) ℝ) (k : Fin J)
    (hk : ∀ i j, j ≠ k → Δ₁ i j = Δ₂ i j) (lam : ℝ) :
    (G * (lam • Δ₁ + (1 - lam) • Δ₂)).det =
      lam * (G * Δ₁).det + (1 - lam) * (G * Δ₂).det := by
  set X₁ := G * Δ₁
  set X₂ := G * Δ₂
  have h2 : X₂ = updateCol X₁ k (fun i => X₂ i k) := by
    ext i j
    by_cases hj : j = k
    · subst hj; simp
    · rw [updateCol_ne hj]
      simp only [X₁, X₂, mul_apply]
      exact Finset.sum_congr rfl (fun l _ => by rw [hk l j hj])
  have h3 : G * (lam • Δ₁ + (1 - lam) • Δ₂) =
      updateCol X₁ k (lam • (fun i => X₁ i k) + (1 - lam) • (fun i => X₂ i k)) := by
    ext i j
    by_cases hj : j = k
    · subst hj
      simp only [updateCol_self, X₁, X₂, Matrix.mul_add, Matrix.mul_smul, Matrix.add_apply,
        Matrix.smul_apply, Pi.add_apply, Pi.smul_apply]
    · rw [updateCol_ne hj]
      simp only [X₁, Matrix.mul_add, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      have : (G * Δ₂) i j = (G * Δ₁) i j := by
        simp only [mul_apply]
        exact Finset.sum_congr rfl (fun l _ => by rw [hk l j hj])
      rw [this]; ring
  rw [h3, det_updateCol_add, det_updateCol_smul, det_updateCol_smul]
  have e1 : updateCol X₁ k (fun i => X₁ i k) = X₁ := by
    ext i j
    by_cases hj : j = k
    · subst hj; simp
    · rw [updateCol_ne hj]
  rw [e1, ← h2]

theorem neighbors_det {J K : ℕ} (N : Network J K) (Δ₁ Δ₂ : Matrix (Fin K) (Fin J) ℝ)
    (hnb : AreNeighbors ![Δ₁, Δ₂]) (lam : ℝ) :
    (reflInv N (lam • Δ₁ + (1 - lam) • Δ₂)).det =
      lam * (reflInv N Δ₁).det + (1 - lam) * (reflInv N Δ₂).det := by
  unfold reflInv
  by_cases hS : ∃ k, ∃ i, Δ₁ i k ≠ Δ₂ i k
  · obtain ⟨k, i₀, hi₀⟩ := hS
    apply det_mul_comb_of_col _ _ _ k
    intro i j hj
    by_contra hne
    have hjS : j ∈ ({j | ∃ a b k, (![Δ₁, Δ₂] : Fin 2 → Matrix (Fin K) (Fin J) ℝ) a k j ≠
        (![Δ₁, Δ₂] : Fin 2 → Matrix (Fin K) (Fin J) ℝ) b k j} : Set (Fin J)) :=
      ⟨0, 1, i, by simpa using hne⟩
    have hkS : k ∈ ({j | ∃ a b k, (![Δ₁, Δ₂] : Fin 2 → Matrix (Fin K) (Fin J) ℝ) a k j ≠
        (![Δ₁, Δ₂] : Fin 2 → Matrix (Fin K) (Fin J) ℝ) b k j} : Set (Fin J)) :=
      ⟨0, 1, i₀, by simpa using hi₀⟩
    exact hj (hnb hjS hkS)
  · push Not at hS
    have he : Δ₂ = Δ₁ := by ext i j; exact (hS j i).symm
    subst he
    have : lam • Δ₂ + (1 - lam) • Δ₂ = Δ₂ := by
      rw [← add_smul]; simp
    rw [this]; ring

theorem neighbors_triple {J K : ℕ} (Δ₁ Δ₂ : Matrix (Fin K) (Fin J) ℝ)
    (hnb : AreNeighbors ![Δ₁, Δ₂]) (lam : ℝ) :
    AreNeighbors ![Δ₁, Δ₂, lam • Δ₁ + (1 - lam) • Δ₂] := by
  unfold AreNeighbors at *
  refine Set.Subsingleton.anti hnb ?_
  rintro j ⟨a, b, k, hab⟩
  by_contra hcon
  have h12 : Δ₁ k j = Δ₂ k j := by
    by_contra h
    exact hcon ⟨0, 1, k, by simpa using h⟩
  apply hab
  fin_cases a <;> fin_cases b <;> simp [h12] <;> ring

end RQRLemma3Aux

open RobustQueueRatio.SPStability in
theorem solution {J K : ℕ} (N : Network J K) (Δ₁ Δ₂ : Matrix (Fin K) (Fin J) ℝ) (lam : ℝ)
    (hΔ₁ : IsRatioMatrix N Δ₁) (hΔ₂ : IsRatioMatrix N Δ₂) (hnb : AreNeighbors ![Δ₁, Δ₂])
    (hlam₀ : 0 < lam) (hlam₁ : lam < 1)
    (h₁ : IsUnit (reflInv N Δ₁).det) (h₂ : IsUnit (reflInv N Δ₂).det)
    (hsign : 0 < (reflInv N Δ₁).det * (reflInv N Δ₂).det) :
    AreNeighbors ![Δ₁, Δ₂, lam • Δ₁ + (1 - lam) • Δ₂] ∧
      IsUnit (reflInv N (lam • Δ₁ + (1 - lam) • Δ₂)).det := by
  refine ⟨RQRLemma3Aux.neighbors_triple Δ₁ Δ₂ hnb lam, ?_⟩
  rw [RQRLemma3Aux.neighbors_det N Δ₁ Δ₂ hnb lam, isUnit_iff_ne_zero]
  set d₁ := (reflInv N Δ₁).det
  set d₂ := (reflInv N Δ₂).det
  rcases lt_or_gt_of_ne (show d₁ ≠ 0 by rintro h; simp [h] at hsign) with h | h
  · have : d₂ < 0 := by
      by_contra h'; push Not at h'; nlinarith
    nlinarith
  · have : 0 < d₂ := by
      by_contra h'; push Not at h'; nlinarith
    nlinarith
