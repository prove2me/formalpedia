-- Prove2me | solution 1 for RobustSpecClust.Round.U0_isTopEigvecs
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-17T10:46:43.374974+00:00
-- url     : https://prove2.me/submissions/14b369a3-4a93-432a-b492-f72f9a4e0f4f

import Definitions.Def_RobustSpecClust_Round_Setting

open RobustSpecClust.Round Matrix

theorem solution {n r : ℕ} (φ : Fin n → Fin r) (hφ : ∀ k, 0 < clusterSize φ k) :
    IsTopEigvecsWith (trueClust φ) (U0 φ) (fun k => (clusterSize φ k : ℝ)) ∧
      ∀ v : Fin n → ℝ, (U0 φ)ᵀ *ᵥ v = 0 → trueClust φ *ᵥ v = 0 := by
  -- `s k = √n_k`, positive since every cluster is nonempty
  have hs : ∀ k, 0 < Real.sqrt (clusterSize φ k) := fun k =>
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hφ k))
  have hss : ∀ k, Real.sqrt (clusterSize φ k) * Real.sqrt (clusterSize φ k)
      = (clusterSize φ k : ℝ) := fun k => Real.mul_self_sqrt (Nat.cast_nonneg _)
  -- sums over a cluster
  have hcard : ∀ k, ∑ i : Fin n, (if φ i = k then (1 : ℝ) else 0) = clusterSize φ k := by
    intro k
    rw [Finset.sum_boole]
    rfl
  -- `(U⁰)ᵀ v` is the scaled cluster sum of `v`
  have hUTv : ∀ (v : Fin n → ℝ) k, ((U0 φ)ᵀ *ᵥ v) k
      = 1 / Real.sqrt (clusterSize φ k) * ∑ i, (if φ i = k then v i else 0) := by
    intro v k
    simp only [mulVec, dotProduct, transpose_apply, U0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  -- `X⁰ v` sums `v` over the cluster of each row
  have hXv : ∀ (v : Fin n → ℝ) i, (trueClust φ *ᵥ v) i
      = ∑ j, (if φ j = φ i then v j else 0) := by
    intro v i
    simp only [mulVec, dotProduct, trueClust]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : φ i = φ j
    · simp [h]
    · simp [h, Ne.symm h]
  have hker : ∀ v : Fin n → ℝ, (U0 φ)ᵀ *ᵥ v = 0 → trueClust φ *ᵥ v = 0 := by
    intro v hv
    funext i
    have h := congrFun hv (φ i)
    rw [hUTv] at h
    rw [hXv, Pi.zero_apply]
    have hne : (1 / Real.sqrt (clusterSize φ (φ i))) ≠ 0 := by
      have := hs (φ i); positivity
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hne
    · exact h0
  refine ⟨⟨?_, ?_, ?_⟩, hker⟩
  · -- orthonormal columns
    ext k k'
    simp only [mul_apply, transpose_apply, U0, one_apply]
    by_cases hkk : k = k'
    · subst hkk
      have : ∀ i, (if φ i = k then 1 / Real.sqrt (clusterSize φ k) else 0)
          * (if φ i = k then 1 / Real.sqrt (clusterSize φ k) else 0)
          = (if φ i = k then (1 : ℝ) else 0) * (1 / (clusterSize φ k : ℝ)) := by
        intro i
        split_ifs
        · rw [one_mul, div_mul_div_comm, one_mul, hss]
        · simp
      simp only [this, ← Finset.sum_mul, hcard, if_true]
      have := hφ k
      field_simp
    · rw [if_neg hkk]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases h : φ i = k
      · have : φ i ≠ k' := h ▸ hkk
        simp [h, hkk]
      · simp [h]
  · -- eigenvector equation `X⁰ U⁰ = U⁰ Diag(n_k)`
    ext i k
    rw [mul_diagonal, mul_apply]
    simp only [trueClust, U0]
    have : ∀ j, (if φ i = φ j then (1 : ℝ) else 0)
        * (if φ j = k then 1 / Real.sqrt (clusterSize φ k) else 0)
        = (if φ i = k then 1 / Real.sqrt (clusterSize φ k) else 0)
          * (if φ j = k then (1 : ℝ) else 0) := by
      intro j
      by_cases hj : φ j = k
      · by_cases hi : φ i = k
        · simp [hi, hj]
        · simp [hi, hj]
      · simp [hj]
    simp only [this, ← Finset.mul_sum, hcard]
  · -- the Rayleigh quotient on the complement vanishes
    intro v hv k
    rw [hker v hv, dotProduct_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i))
