-- Prove2me | solution 1 for RobustQueueRatio.SPStability.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:13:49.939695+00:00
-- url     : https://prove2.me/submissions/e4d03679-97a1-44c0-ab4e-0d82341b76f7

import Mathlib
import Definitions.Def_RobustQueueRatio_SPStability_Network
import Definitions.Def_RobustQueueRatio_SPStability_ChenS
import Definitions.Def_RobustQueueRatio_SPStability_RatioMatrix

open Matrix

namespace RQRThm6Aux

open RobustQueueRatio.SPStability

/-- The determinant is affine along a segment of square matrices that agree outside one
column. -/
theorem det_comb_col {J : ℕ} (X₁ X₂ : Matrix (Fin J) (Fin J) ℝ) (k : Fin J)
    (hk : ∀ i j, j ≠ k → X₁ i j = X₂ i j) (lam : ℝ) :
    (lam • X₁ + (1 - lam) • X₂).det = lam * X₁.det + (1 - lam) * X₂.det := by
  have h2 : X₂ = updateCol X₁ k (fun i => X₂ i k) := by
    ext i j
    by_cases hj : j = k
    · subst hj; simp
    · rw [updateCol_ne hj]; exact (hk i j hj).symm
  have h3 : lam • X₁ + (1 - lam) • X₂ =
      updateCol X₁ k (lam • (fun i => X₁ i k) + (1 - lam) • (fun i => X₂ i k)) := by
    ext i j
    by_cases hj : j = k
    · subst hj; simp
    · rw [updateCol_ne hj]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [← hk i j hj]; ring
  have e1 : updateCol X₁ k (fun i => X₁ i k) = X₁ := by
    ext i j
    by_cases hj : j = k
    · subst hj; simp
    · rw [updateCol_ne hj]
  rw [h3, det_updateCol_add, det_updateCol_smul, det_updateCol_smul, e1, ← h2]

/-- The adjugate is affine along a segment of square matrices that agree outside one column. -/
theorem adjugate_comb_col {J : ℕ} (X₁ X₂ : Matrix (Fin J) (Fin J) ℝ) (k : Fin J)
    (hk : ∀ i j, j ≠ k → X₁ i j = X₂ i j) (lam : ℝ) :
    adjugate (lam • X₁ + (1 - lam) • X₂) = lam • adjugate X₁ + (1 - lam) • adjugate X₂ := by
  ext i j
  simp only [adjugate_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hrow : updateRow (lam • X₁ + (1 - lam) • X₂) j (Pi.single i 1) =
      lam • updateRow X₁ j (Pi.single i 1) + (1 - lam) • updateRow X₂ j (Pi.single i 1) := by
    ext r c
    by_cases hr : r = j
    · subst hr; simp only [updateRow_self, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    · simp [updateRow_ne hr]
  rw [hrow]
  apply det_comb_col
  intro r c hc
  by_cases hr : r = j
  · subst hr; simp
  · simp only [updateRow_ne hr]; exact hk r c hc

theorem cols_agree {J K : ℕ} (G : Matrix (Fin J) (Fin K) ℝ) (Δ₁ Δ₂ : Matrix (Fin K) (Fin J) ℝ)
    (k : Fin J) (hk : ∀ i j, j ≠ k → Δ₁ i j = Δ₂ i j) :
    ∀ i j, j ≠ k → (G * Δ₁) i j = (G * Δ₂) i j := by
  intro i j hj
  simp only [mul_apply]
  exact Finset.sum_congr rfl (fun l _ => by rw [hk l j hj])

/-- Determinant and adjugate of `CMQΔ` are affine along a neighbor segment. -/
theorem neighbors_affine {J K : ℕ} (N : Network J K) (Δ₁ Δ₂ : Matrix (Fin K) (Fin J) ℝ)
    (hnb : AreNeighbors ![Δ₁, Δ₂]) (lam : ℝ) :
    (reflInv N (lam • Δ₁ + (1 - lam) • Δ₂)).det =
        lam * (reflInv N Δ₁).det + (1 - lam) * (reflInv N Δ₂).det ∧
      adjugate (reflInv N (lam • Δ₁ + (1 - lam) • Δ₂)) =
        lam • adjugate (reflInv N Δ₁) + (1 - lam) • adjugate (reflInv N Δ₂) := by
  have hB : reflInv N (lam • Δ₁ + (1 - lam) • Δ₂) =
      lam • reflInv N Δ₁ + (1 - lam) • reflInv N Δ₂ := by
    unfold reflInv; rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  rw [hB]
  by_cases hS : ∃ k, ∃ i, Δ₁ i k ≠ Δ₂ i k
  · obtain ⟨k, i₀, hi₀⟩ := hS
    have hk : ∀ i j, j ≠ k → Δ₁ i j = Δ₂ i j := by
      intro i j hj
      by_contra hne
      have hjS : j ∈ ({j | ∃ a b k, (![Δ₁, Δ₂] : Fin 2 → Matrix (Fin K) (Fin J) ℝ) a k j ≠
          (![Δ₁, Δ₂] : Fin 2 → Matrix (Fin K) (Fin J) ℝ) b k j} : Set (Fin J)) :=
        ⟨0, 1, i, by simpa using hne⟩
      have hkS : k ∈ ({j | ∃ a b k, (![Δ₁, Δ₂] : Fin 2 → Matrix (Fin K) (Fin J) ℝ) a k j ≠
          (![Δ₁, Δ₂] : Fin 2 → Matrix (Fin K) (Fin J) ℝ) b k j} : Set (Fin J)) :=
        ⟨0, 1, i₀, by simpa using hi₀⟩
      exact hj (hnb hjS hkS)
    have hX := cols_agree (N.C * N.M * N.Q) Δ₁ Δ₂ k hk
    exact ⟨det_comb_col _ _ k hX lam, adjugate_comb_col _ _ k hX lam⟩
  · push Not at hS
    have he : Δ₂ = Δ₁ := by ext i j; exact (hS j i).symm
    subst he
    have : lam • reflInv N Δ₂ + (1 - lam) • reflInv N Δ₂ = reflInv N Δ₂ := by
      rw [← add_smul]; simp
    rw [this]
    refine ⟨by ring, ?_⟩
    rw [← add_smul]; simp

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

theorem refl_eq {J K : ℕ} (N : Network J K) (Δ : Matrix (Fin K) (Fin J) ℝ) :
    RobustQueueRatio.SPStability.refl N Δ = ((reflInv N Δ).det)⁻¹ • adjugate (reflInv N Δ) := by
  unfold RobustQueueRatio.SPStability.refl; rw [inv_def, Ring.inverse_eq_inv']

theorem det_refl {J K : ℕ} (N : Network J K) (Δ : Matrix (Fin K) (Fin J) ℝ) :
    (RobustQueueRatio.SPStability.refl N Δ).det = ((reflInv N Δ).det)⁻¹ := by
  unfold RobustQueueRatio.SPStability.refl; rw [det_nonsing_inv, Ring.inverse_eq_inv']

end RQRThm6Aux

open RobustQueueRatio.SPStability RQRThm6Aux in
theorem solution {J K : ℕ} (N : Network J K) (Δ₁ Δ₂ : Matrix (Fin K) (Fin J) ℝ) (lam : ℝ)
    (hΔ₁ : IsRatioMatrix N Δ₁) (hΔ₂ : IsRatioMatrix N Δ₂) (hnb : AreNeighbors ![Δ₁, Δ₂])
    (hlam₀ : 0 < lam) (hlam₁ : lam < 1)
    (h₁ : IsUnit (reflInv N Δ₁).det) (h₂ : IsUnit (reflInv N Δ₂).det)
    (h₃ : IsUnit (reflInv N (lam • Δ₁ + (1 - lam) • Δ₂)).det) :
    let Δ₃ := lam • Δ₁ + (1 - lam) • Δ₂
    let β := lam * (refl N Δ₂).det / (lam * (refl N Δ₂).det + (1 - lam) * (refl N Δ₁).det)
    AreNeighbors ![Δ₁, Δ₂, Δ₃] ∧
      refl N Δ₃ = β • refl N Δ₁ + (1 - β) • refl N Δ₂ ∧
      ((refl N Δ₃).det)⁻¹ • refl N Δ₃ =
        lam • (((refl N Δ₁).det)⁻¹ • refl N Δ₁) +
          (1 - lam) • (((refl N Δ₂).det)⁻¹ • refl N Δ₂) ∧
      (0 < (refl N Δ₁).det * (refl N Δ₂).det → 0 < β ∧ β < 1) := by
  intro Δ₃ β
  obtain ⟨hdet, hadj⟩ := neighbors_affine N Δ₁ Δ₂ hnb lam
  have hb₁ : (reflInv N Δ₁).det ≠ 0 := h₁.ne_zero
  have hb₂ : (reflInv N Δ₂).det ≠ 0 := h₂.ne_zero
  have hb₃ : (reflInv N Δ₃).det ≠ 0 := h₃.ne_zero
  have hβ : β = lam * (reflInv N Δ₁).det / (reflInv N Δ₃).det := by
    simp only [β, det_refl]
    rw [hdet] at hb₃ ⊢
    field_simp
  have h1β : 1 - β = (1 - lam) * (reflInv N Δ₂).det / (reflInv N Δ₃).det := by
    rw [hβ, eq_div_iff hb₃, sub_mul, div_mul_cancel₀ _ hb₃, hdet]; ring
  refine ⟨neighbors_triple Δ₁ Δ₂ hnb lam, ?_, ?_, ?_⟩
  · rw [refl_eq, refl_eq, refl_eq, hadj, h1β, hβ, smul_add, smul_smul, smul_smul, smul_smul,
      smul_smul]
    congr 2
    · field_simp
    · field_simp
  · rw [det_refl, det_refl, det_refl, inv_inv, inv_inv, inv_inv, refl_eq, refl_eq, refl_eq, hadj]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    field_simp
  · intro hpos
    rw [det_refl, det_refl, ← mul_inv] at hpos
    have hprod : 0 < (reflInv N Δ₁).det * (reflInv N Δ₂).det := inv_pos.1 hpos
    have h1l : 0 < 1 - lam := by linarith
    rw [hβ]
    have hd3 : (reflInv N Δ₃).det = lam * (reflInv N Δ₁).det + (1 - lam) * (reflInv N Δ₂).det :=
      hdet
    rcases lt_or_gt_of_ne hb₁ with h | h
    · have h2 : (reflInv N Δ₂).det < 0 := by
        by_contra h'; push Not at h'; nlinarith
      have h3 : (reflInv N Δ₃).det < 0 := by rw [hd3]; nlinarith
      constructor
      · apply div_pos_of_neg_of_neg _ h3; nlinarith
      · rw [div_lt_one_of_neg h3, hd3]; nlinarith
    · have h2 : 0 < (reflInv N Δ₂).det := by
        by_contra h'; push Not at h'; nlinarith
      have h3 : 0 < (reflInv N Δ₃).det := by rw [hd3]; nlinarith
      constructor
      · apply div_pos _ h3; nlinarith
      · rw [div_lt_one h3, hd3]; nlinarith
