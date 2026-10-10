-- Prove2me | solution 1 for WallGSL.unital_positive_map_eigenvalue_majorization
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-10T05:29:51.867691+00:00
-- url     : https://prove2.me/submissions/b303314c-077d-4ffc-b7f1-896955f53e84

import Mathlib

open Matrix
open scoped ComplexOrder

lemma knap {n : ℕ} (lam c : Fin n → ℝ) (hc0 : ∀ k, 0 ≤ c k) (hc1 : ∀ k, c k ≤ 1)
    (i : ℕ) (hi : i ≤ n) (hsum : ∑ k, c k = i) :
    ∃ t : Finset (Fin n), t.card = i ∧ ∑ k, lam k * c k ≤ ∑ j ∈ t, lam j := by
  have hne : (Finset.powersetCard i (Finset.univ : Finset (Fin n))).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr; simpa using hi
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image _ (fun t => ∑ j ∈ t, lam j) hne
  have htc : t.card = i := (Finset.mem_powersetCard.mp ht).2
  refine ⟨t, htc, ?_⟩
  have hex : ∀ a ∈ t, ∀ b ∉ t, lam b ≤ lam a := by
    intro a ha b hb
    by_contra h
    push Not at h
    have hmem : insert b (t.erase a) ∈ Finset.powersetCard i Finset.univ := by
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_insert_of_notMem (by simp [hb]), Finset.card_erase_of_mem ha, htc]
      have : 0 < i := htc ▸ Finset.card_pos.mpr ⟨a, ha⟩
      omega
    have := hmax _ hmem
    rw [Finset.sum_insert (by simp [hb]), ← Finset.add_sum_erase t lam ha] at this
    linarith
  have split : ∑ k, lam k * c k = ∑ k ∈ t, lam k * c k + ∑ k ∈ tᶜ, lam k * c k :=
    (Finset.sum_add_sum_compl t _).symm
  have splitc : ∑ k ∈ t, c k + ∑ k ∈ tᶜ, c k = i := by
    rw [Finset.sum_add_sum_compl]; exact hsum
  by_cases hT : t.Nonempty
  · set m := t.inf' hT lam
    have h1 : ∑ k ∈ tᶜ, lam k * c k ≤ ∑ k ∈ tᶜ, m * c k := by
      apply Finset.sum_le_sum; intro b hb
      apply mul_le_mul_of_nonneg_right _ (hc0 b)
      apply Finset.le_inf'; intro a ha; exact hex a ha b (Finset.mem_compl.mp hb)
    have h2 : ∑ k ∈ t, m * (1 - c k) ≤ ∑ k ∈ t, lam k * (1 - c k) := by
      apply Finset.sum_le_sum; intro a ha
      apply mul_le_mul_of_nonneg_right (Finset.inf'_le _ ha); linarith [hc1 a]
    have h3 : ∑ k ∈ t, (1 - c k) = ∑ k ∈ tᶜ, c k := by
      rw [Finset.sum_sub_distrib]; simp [htc]; linarith
    rw [← Finset.mul_sum] at h1 h2
    rw [h3] at h2
    have h4 : ∑ k ∈ t, lam k * (1 - c k) = ∑ k ∈ t, lam k - ∑ k ∈ t, lam k * c k := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro k _; ring
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hT
    subst hT
    simp at htc
    subst htc
    have : ∀ k, c k = 0 := by
      intro k
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hc0 k)).mp (by simpa using hsum) k
      simpa using this
    simp [this]

theorem solution
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hT_pos : ∀ A : Matrix (Fin n) (Fin n) ℂ, A.PosSemidef → (T A).PosSemidef)
    (hT_trace : ∀ A : Matrix (Fin n) (Fin n) ℂ, (T A).trace = A.trace)
    (hT_one : T 1 = 1)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosSemidef) (hρ_tr : ρ.trace = 1)
    (i : ℕ) (s : Finset (Fin n)) (hs : s.card = i) :
    ∃ t : Finset (Fin n), t.card = i ∧
      ∑ j ∈ s, (hT_pos ρ hρ).isHermitian.eigenvalues j ≤ ∑ j ∈ t, hρ.isHermitian.eigenvalues j := by
  set hB := (hT_pos ρ hρ).isHermitian
  set U : Matrix (Fin n) (Fin n) ℂ := (hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  set V : Matrix (Fin n) (Fin n) ℂ := (hρ.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hVV : star V * V = 1 := Unitary.coe_star_mul_self _
  have hVV' : V * star V = 1 := Unitary.coe_mul_star_self _
  let f : Matrix (Fin n) (Fin n) ℂ → ℝ := fun X => ∑ j ∈ s, ((star U * X * U) j j).re
  let g : Matrix (Fin n) (Fin n) ℂ → ℝ := fun X => ∑ j ∈ sᶜ, ((star U * X * U) j j).re
  have hdiag : star U * T ρ * U = diagonal (RCLike.ofReal ∘ hB.eigenvalues) := by
    have := hB.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, mul_assoc] using this
  have hfB : f (T ρ) = ∑ j ∈ s, hB.eigenvalues j := by
    simp only [f, hdiag]; simp
  have hf_nonneg : ∀ X : Matrix (Fin n) (Fin n) ℂ, X.PosSemidef → 0 ≤ f X ∧ 0 ≤ g X := by
    intro X hX
    have hP : (star U * X * U).PosSemidef := by
      have := hX.conjTranspose_mul_mul_same U
      simpa [Matrix.star_eq_conjTranspose] using this
    have hd : ∀ j, 0 ≤ ((star U * X * U) j j).re := fun j =>
      (Complex.nonneg_iff.mp hP.diag_nonneg).1
    exact ⟨Finset.sum_nonneg fun j _ => hd j, Finset.sum_nonneg fun j _ => hd j⟩
  have hfg : ∀ X, f X + g X = (X.trace).re := by
    intro X
    simp only [f, g]
    rw [Finset.sum_add_sum_compl, ← Complex.re_sum]
    have : ∑ j, (star U * X * U) j j = (star U * X * U).trace := rfl
    rw [this, Matrix.trace_mul_cycle, hUU', one_mul]
  -- spectral pieces of ρ
  let P : Fin n → Matrix (Fin n) (Fin n) ℂ := fun k => V * diagonal (Pi.single k 1) * star V
  have hPpsd : ∀ k, (P k).PosSemidef := by
    intro k
    have h0 : (diagonal (Pi.single k (1:ℂ))).PosSemidef := by
      apply PosSemidef.diagonal
      intro j; by_cases h : j = k
      · subst h; simp
      · simp [Pi.single_apply, h]
    simpa [P, Matrix.star_eq_conjTranspose] using h0.mul_mul_conjTranspose_same V
  have hPtr : ∀ k, (P k).trace = 1 := by
    intro k
    simp only [P]
    rw [Matrix.trace_mul_cycle, hVV, one_mul, trace_diagonal]
    simp
  have hPsum : ∑ k, P k = 1 := by
    simp only [P]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    have : ∑ k : Fin n, diagonal (Pi.single k (1:ℂ)) = 1 := by
      ext a b
      simp [Matrix.sum_apply, diagonal_apply, Matrix.one_apply, Pi.single_apply]
    rw [this, mul_one, hVV']
  have hρdecomp : ρ = ∑ k, ((hρ.isHermitian.eigenvalues k : ℝ) : ℂ) • P k := by
    have hs := hρ.isHermitian.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    conv_lhs => rw [hs]
    simp only [P]
    rw [show diagonal (RCLike.ofReal ∘ hρ.isHermitian.eigenvalues) =
        ∑ k, ((hρ.isHermitian.eigenvalues k : ℝ) : ℂ) • diagonal (Pi.single k (1:ℂ)) by
      ext a b
      simp [Matrix.sum_apply, diagonal_apply, Pi.single_apply]]
    simp [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]; rfl
  let c : Fin n → ℝ := fun k => f (T (P k))
  have hc0 : ∀ k, 0 ≤ c k := fun k => (hf_nonneg _ (hT_pos _ (hPpsd k))).1
  have hc1 : ∀ k, c k ≤ 1 := by
    intro k
    have h1 := hfg (T (P k))
    have h2 := (hf_nonneg _ (hT_pos _ (hPpsd k))).2
    rw [hT_trace, hPtr] at h1
    simp only [c]; simp at h1; linarith
  have hflin : ∀ (a : Fin n → ℝ) (Y : Fin n → Matrix (Fin n) (Fin n) ℂ),
      f (∑ k, ((a k : ℝ) : ℂ) • Y k) = ∑ k, a k * f (Y k) := by
    intro a Y
    simp only [f, Finset.mul_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Complex.re_sum, smul_eq_mul,
      Complex.re_ofReal_mul]
    exact Finset.sum_comm
  have hsumc : ∑ k, c k = i := by
    have := hflin (fun _ => 1) (fun k => T (P k))
    simp only [Complex.ofReal_one, one_smul, one_mul] at this
    simp only [c]
    rw [← this, ← map_sum, hPsum, hT_one]
    simp only [f, mul_one, hUU]
    simp [Matrix.one_apply, hs]
  have hi : i ≤ n := by rw [← hs]; simpa using s.card_le_univ
  obtain ⟨t, htc, ht⟩ := knap hρ.isHermitian.eigenvalues c hc0 hc1 i hi hsumc
  refine ⟨t, htc, ?_⟩
  rw [← hfB]
  have : f (T ρ) = ∑ k, hρ.isHermitian.eigenvalues k * c k := by
    conv_lhs => rw [hρdecomp]
    rw [map_sum]
    simp only [map_smul]
    exact hflin _ _
  rw [this]; exact ht
