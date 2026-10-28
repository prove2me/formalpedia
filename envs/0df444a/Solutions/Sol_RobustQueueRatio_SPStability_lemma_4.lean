-- Prove2me | solution 1 for RobustQueueRatio.SPStability.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:20:39.384695+00:00
-- url     : https://prove2.me/submissions/f0f2de5b-6c2f-477a-bac8-79512e89f5b2

import Mathlib
import Definitions.Def_RobustQueueRatio_SPStability_Network
import Definitions.Def_RobustQueueRatio_SPStability_ChenS
import Definitions.Def_RobustQueueRatio_SPStability_RatioMatrix

open Matrix

namespace RQRLem4Aux

variable {J : ℕ}

/-- `X = u e_kᵀ R` squares to `s X` with `s = (R u)_k`. -/
theorem X_sq (R : Matrix (Fin J) (Fin J) ℝ) (u : Fin J → ℝ) (k : Fin J) :
    (vecMulVec u (Pi.single k 1) * R) * (vecMulVec u (Pi.single k 1) * R) =
      (R *ᵥ u) k • (vecMulVec u (Pi.single k 1) * R) := by
  have hX : ∀ i j, (vecMulVec u (Pi.single k 1) * R) i j = u i * R k j := by
    intro i j
    simp [mul_apply, vecMulVec_apply, Pi.single_apply]
  ext i j
  rw [mul_apply, Matrix.smul_apply, hX, smul_eq_mul]
  simp only [hX, mulVec, dotProduct]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun l _ => by ring)

/-- Rank-one update in column `k`: determinant and inverse (Sherman–Morrison). -/
theorem rank_one (B : Matrix (Fin J) (Fin J) ℝ) (hB : IsUnit B.det) (u : Fin J → ℝ)
    (k : Fin J) (c : ℝ) :
    (B + c • vecMulVec u (Pi.single k 1)).det = B.det * (1 + c * (B⁻¹ *ᵥ u) k) ∧
      (1 + c * (B⁻¹ *ᵥ u) k ≠ 0 →
        (B + c • vecMulVec u (Pi.single k 1))⁻¹ =
          B⁻¹ * (1 - c • ((1 + c * (B⁻¹ *ᵥ u) k)⁻¹ • (vecMulVec u (Pi.single k 1) * B⁻¹)))) := by
  constructor
  · have : c • vecMulVec u (Pi.single k 1) =
        replicateCol Unit (c • u) * replicateRow Unit (Pi.single k (1 : ℝ)) := by
      rw [← vecMulVec_eq]; ext i j; simp [vecMulVec_apply, mul_assoc]
    rw [this, det_add_replicateCol_mul_replicateRow hB]
    congr 1
    rw [Matrix.det_unique]
    simp only [Matrix.add_apply, Matrix.one_apply_eq, mul_apply, replicateRow_apply,
      replicateCol_apply, Finset.univ_unique, Finset.sum_singleton]
    simp [Pi.single_apply, mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  · intro hD
    set D := 1 + c * (B⁻¹ *ᵥ u) k
    set X := vecMulVec u (Pi.single k 1) * B⁻¹
    apply inv_eq_right_inv
    have h1 : (B + c • vecMulVec u (Pi.single k 1)) * B⁻¹ = 1 + c • X := by
      rw [Matrix.add_mul, mul_nonsing_inv _ hB, Matrix.smul_mul]
    rw [← Matrix.mul_assoc, h1, Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, X_sq]
    have : c • (c • (D⁻¹ • ((B⁻¹ *ᵥ u) k • X))) = (c * c * D⁻¹ * (B⁻¹ *ᵥ u) k) • X := by
      simp only [smul_smul]; ring_nf
    rw [this]
    have hs : c • X - c • (D⁻¹ • X) - (c * c * D⁻¹ * (B⁻¹ *ᵥ u) k) • X =
        (c - c * D⁻¹ - c * c * D⁻¹ * (B⁻¹ *ᵥ u) k) • X := by
      simp only [smul_smul, sub_smul]
    have hz : c - c * D⁻¹ - c * c * D⁻¹ * (B⁻¹ *ᵥ u) k = 0 := by
      have : c - c * D⁻¹ - c * c * D⁻¹ * (B⁻¹ *ᵥ u) k = c * (1 - D⁻¹ * D) := by
        simp only [D]; ring
      rw [this, inv_mul_cancel₀ hD]; ring
    calc 1 - c • (D⁻¹ • X) + (c • X - (c * c * D⁻¹ * (B⁻¹ *ᵥ u) k) • X)
        = 1 + (c • X - c • (D⁻¹ • X) - (c * c * D⁻¹ * (B⁻¹ *ᵥ u) k) • X) := by abel
      _ = 1 := by rw [hs, hz, zero_smul, add_zero]

end RQRLem4Aux

open RobustQueueRatio.SPStability RQRLem4Aux in
theorem solution {J K : ℕ} (N : Network J K) (Δ₁ Δ₂ : Matrix (Fin K) (Fin J) ℝ) (k : Fin J)
    (lam : ℝ) (hΔ₁ : IsRatioMatrix N Δ₁) (hΔ₂ : IsRatioMatrix N Δ₂)
    (hk : ∀ i j, j ≠ k → Δ₁ i j = Δ₂ i j) (hlam₀ : 0 < lam) (hlam₁ : lam < 1)
    (h₁ : IsUnit (reflInv N Δ₁).det) (h₂ : IsUnit (reflInv N Δ₂).det)
    (h₃ : IsUnit (reflInv N (lam • Δ₁ + (1 - lam) • Δ₂)).det) :
    let Δ₃ := lam • Δ₁ + (1 - lam) • Δ₂
    let u : Fin J → ℝ := fun i => reflInv N (Δ₂ - Δ₁) i k
    let v : Fin J → ℝ := Pi.single k 1
    let A₁ := (1 + (1 - lam) * (v ⬝ᵥ (refl N Δ₁ *ᵥ u)))⁻¹ • (vecMulVec u v * refl N Δ₁)
    let A₂ := (1 - lam * (v ⬝ᵥ (refl N Δ₂ *ᵥ u)))⁻¹ • (vecMulVec u v * refl N Δ₂)
    AreNeighbors ![Δ₁, Δ₂, Δ₃] ∧
      refl N Δ₁ k = ((reflInv N Δ₂).det / (reflInv N Δ₁).det) • refl N Δ₂ k ∧
      A₁ = A₂ ∧
      refl N Δ₃ = refl N Δ₁ * (1 - (1 - lam) • A₁) ∧
      refl N Δ₃ = refl N Δ₂ * (1 + lam • A₁) := by
  intro Δ₃ u v A₁ A₂
  set B₁ := reflInv N Δ₁ with hB₁
  set B₂ := reflInv N Δ₂ with hB₂
  -- the difference of the two `CMQΔ` matrices is `u vᵀ`
  have hdiff : reflInv N (Δ₂ - Δ₁) = vecMulVec u v := by
    ext i j
    simp only [vecMulVec_apply, v, Pi.single_apply]
    by_cases hj : j = k
    · subst hj; simp [u]
    · simp only [hj, if_false, mul_zero]
      simp only [reflInv, mul_apply, Matrix.sub_apply]
      exact Finset.sum_eq_zero (fun l _ => by rw [hk l j hj, sub_self, mul_zero])
  have hsplit : ∀ Δ Δ' : Matrix (Fin K) (Fin J) ℝ, ∀ a b : ℝ,
      reflInv N (a • Δ + b • Δ') = a • reflInv N Δ + b • reflInv N Δ' := by
    intro Δ Δ' a b; unfold reflInv; rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  have hsub : reflInv N (Δ₂ - Δ₁) = B₂ - B₁ := by
    rw [hB₁, hB₂]; unfold reflInv; rw [Matrix.mul_sub]
  have e2 : B₂ = B₁ + (1 : ℝ) • vecMulVec u v := by rw [one_smul, ← hdiff, hsub]; abel
  have e31 : reflInv N Δ₃ = B₁ + (1 - lam) • vecMulVec u v := by
    rw [hsplit, ← hdiff, hsub, ← hB₁, ← hB₂]; module
  have e32 : reflInv N Δ₃ = B₂ + (-lam) • vecMulVec u v := by
    rw [hsplit, ← hdiff, hsub, ← hB₁, ← hB₂]; module
  have hdot : ∀ w : Fin J → ℝ, v ⬝ᵥ w = w k := by
    intro w; simp [v]
  set s₁ := (B₁⁻¹ *ᵥ u) k
  set s₂ := (B₂⁻¹ *ᵥ u) k
  obtain ⟨d2, -⟩ := rank_one B₁ h₁ u k 1
  obtain ⟨d31, i31⟩ := rank_one B₁ h₁ u k (1 - lam)
  obtain ⟨d32, i32⟩ := rank_one B₂ h₂ u k (-lam)
  rw [← e2] at d2
  rw [← e31] at d31 i31
  rw [← e32] at d32 i32
  have hb₁ := h₁.ne_zero
  have hb₂ := h₂.ne_zero
  have hb₃ := h₃.ne_zero
  have hD1 : 1 + (1 - lam) * s₁ ≠ 0 := by
    intro h; apply hb₃; change (reflInv N Δ₃).det = 0; rw [d31, h, mul_zero]
  have hD2 : 1 + -lam * s₂ ≠ 0 := by
    intro h; apply hb₃; change (reflInv N Δ₃).det = 0; rw [d32, h, mul_zero]
  have hD0 : 1 + 1 * s₁ ≠ 0 := by
    intro h; apply hb₂; rw [d2, h, mul_zero]
  have hD0' : 1 + s₁ ≠ 0 := by simpa using hD0
  have hD2' : 1 + -(lam * s₂) ≠ 0 := by simpa [neg_mul] using hD2
  -- row `k` of the inverses
  have hrow : ∀ j, B₂⁻¹ k j = (1 + 1 * s₁)⁻¹ * B₁⁻¹ k j := by
    obtain ⟨-, i2⟩ := rank_one B₁ h₁ u k 1
    rw [← e2] at i2
    intro j
    rw [i2 hD0]
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, Matrix.mul_smul,
      Matrix.smul_apply, smul_eq_mul, ← Matrix.mul_assoc]
    have : (B₁⁻¹ * vecMulVec u (Pi.single k 1) * B₁⁻¹) k j = s₁ * B₁⁻¹ k j := by
      rw [Matrix.mul_assoc, mul_apply]
      simp only [mul_apply, vecMulVec_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
        ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp only [s₁, mulVec, dotProduct, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun l _ => by ring)
    rw [this]
    change B₁⁻¹ k j - 1 * ((1 + 1 * s₁)⁻¹ * (s₁ * B₁⁻¹ k j)) = (1 + 1 * s₁)⁻¹ * B₁⁻¹ k j
    rw [one_mul, one_mul]
    field_simp
    ring
  have hrow1 : ∀ j, B₁⁻¹ k j = (1 + 1 * s₁) * B₂⁻¹ k j := by
    intro j; rw [hrow, ← mul_assoc, mul_inv_cancel₀ hD0, one_mul]
  have hratio : (1 + 1 * s₁) = B₂.det / B₁.det := by
    rw [d2, mul_div_cancel_left₀ _ hb₁]
  have hA₁ : A₁ = (1 + (1 - lam) * s₁)⁻¹ • (vecMulVec u (Pi.single k 1) * B₁⁻¹) := by
    simp only [A₁, hdot]; rfl
  have hA₂ : A₂ = (1 + -lam * s₂)⁻¹ • (vecMulVec u (Pi.single k 1) * B₂⁻¹) := by
    simp only [A₂, hdot]
    have : (1 - lam * (RobustQueueRatio.SPStability.refl N Δ₂ *ᵥ u) k) = 1 + -lam * s₂ := by
      rw [neg_mul, ← sub_eq_add_neg]; rfl
    rw [this]; rfl
  have hA : A₁ = A₂ := by
    rw [hA₁, hA₂]
    ext i j
    simp only [Matrix.smul_apply, mul_apply, vecMulVec_apply, Pi.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hrow1 j]
    -- scalar identity: (1+s₁)/(1+(1-λ)s₁) = 1/(1-λ s₂)
    have k1 : (1 + (1 - lam) * s₁) * B₁.det = (reflInv N Δ₃).det := by rw [d31]; ring
    have k2 : (1 + -lam * s₂) * B₂.det = (reflInv N Δ₃).det := by rw [d32]; ring
    have k0 : (1 + 1 * s₁) * B₁.det = B₂.det := by rw [d2]; ring
    have : (1 + (1 - lam) * s₁)⁻¹ * (1 + 1 * s₁) = (1 + -lam * s₂)⁻¹ := by
      have hE : (1 + 1 * s₁) * (1 + -lam * s₂) = 1 + (1 - lam) * s₁ := by
        apply mul_right_cancel₀ hb₁
        linear_combination (1 + -lam * s₂) * k0 + k2 - k1
      rw [← hE]
      field_simp
    calc (1 + (1 - lam) * s₁)⁻¹ * (u i * ((1 + 1 * s₁) * B₂⁻¹ k j))
        = ((1 + (1 - lam) * s₁)⁻¹ * (1 + 1 * s₁)) * (u i * B₂⁻¹ k j) := by ring
      _ = _ := by rw [this]
  refine ⟨?_, ?_, hA, ?_, ?_⟩
  · unfold AreNeighbors
    refine Set.Subsingleton.anti (Set.subsingleton_singleton (a := k)) ?_
    rintro j ⟨a, b, l, hab⟩
    by_contra hj
    apply hab
    have hj' : j ≠ k := hj
    have := hk l j hj'
    fin_cases a <;> fin_cases b <;> simp [Δ₃, this] <;> ring
  · ext j
    simp only [Pi.smul_apply, smul_eq_mul]
    change B₁⁻¹ k j = _ * B₂⁻¹ k j
    rw [hrow1, hratio]
  · change (reflInv N Δ₃)⁻¹ = B₁⁻¹ * (1 - (1 - lam) • A₁)
    rw [i31 hD1, hA₁]
  · change (reflInv N Δ₃)⁻¹ = B₂⁻¹ * (1 + lam • A₁)
    rw [i32 hD2, hA, hA₂, neg_smul, sub_neg_eq_add]
