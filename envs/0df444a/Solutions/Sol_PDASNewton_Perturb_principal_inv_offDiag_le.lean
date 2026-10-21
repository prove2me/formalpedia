-- Prove2me | solution 1 for PDASNewton.Perturb.principal_inv_offDiag_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:42:46.068807+00:00
-- url     : https://prove2.me/submissions/efe908b8-2974-4049-9186-58afb70e9a09

import Mathlib
import Definitions.Def_PDASNewton_Perturb_Setting

set_option autoImplicit false
open Matrix

/-- the principal block of an M-matrix is nonsingular with nonnegative inverse -/
lemma pdp_principal_Mmat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : PDASNewton.Perturb.IsMMatrix M) (S : Finset (Fin n)) :
    IsUnit (PDASNewton.MMatrix.principal M S).det ∧
      ∀ i j, 0 ≤ (PDASNewton.MMatrix.principal M S)⁻¹ i j := by
  obtain ⟨hdet, hoff, hinv⟩ := hM
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet
  have hMM' : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  set x : Fin n → ℝ := fun i => ∑ j, M⁻¹ i j with hx
  have hMx : ∀ i, ∑ j, M i j * x j = 1 := by
    intro i
    have : ∑ j, M i j * x j = ∑ k, (M * M⁻¹) i k := by
      simp only [hx, Matrix.mul_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [this]
    simp [hMM, Matrix.one_apply]
  have hxpos : ∀ i, 0 < x i := by
    intro i
    have h0 : 0 ≤ x i := Finset.sum_nonneg (fun j _ => hinv i j)
    rcases h0.eq_or_lt with h | h
    · exfalso
      have hz : ∀ j, M⁻¹ i j = 0 := by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hinv i j)).mp h.symm
        intro j; exact this j (Finset.mem_univ j)
      have h1 : (M⁻¹ * M) i i = 1 := by rw [hMM']; simp
      rw [Matrix.mul_apply] at h1
      simp [hz] at h1
    · exact h
  set P := PDASNewton.MMatrix.principal M S with hP
  set y : S → ℝ := fun i => x i with hy
  have hPy : ∀ i : S, 0 < (P *ᵥ y) i := by
    intro i
    have h1 := hMx i
    rw [← Finset.sum_add_sum_compl S] at h1
    have h2 : ∑ j ∈ Sᶜ, M i j * x j ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      have hij : (i : Fin n) ≠ j := by
        intro h
        have : (j : Fin n) ∈ S := h ▸ i.2
        exact (Finset.mem_compl.mp hj) this
      exact mul_nonpos_of_nonpos_of_nonneg (hoff _ _ hij) (hxpos j).le
    have h3 : (P *ᵥ y) i = ∑ j ∈ S, M i j * x j := by
      simp only [hP, hy, PDASNewton.MMatrix.principal, Matrix.mulVec, dotProduct,
        Matrix.submatrix_apply]
      rw [← Finset.sum_coe_sort S (fun j => M i j * x j)]
    rw [h3]; linarith
  have key : ∀ v : S → ℝ, (∀ i, 0 ≤ (P *ᵥ v) i) → ∀ i, 0 ≤ v i := by
    intro v hv
    by_contra hcon
    push_neg at hcon
    obtain ⟨i1, hi1⟩ := hcon
    have hypos : ∀ j : S, 0 < y j := fun j => hxpos j
    obtain ⟨i0, _, hi0⟩ := Finset.exists_min_image (Finset.univ : Finset S)
      (fun j => v j / y j) ⟨i1, Finset.mem_univ _⟩
    set m : ℝ := v i0 / y i0 with hm
    have hmneg : m < 0 := by
      have := hi0 i1 (Finset.mem_univ _)
      have h2 : v i1 / y i1 < 0 := div_neg_of_neg_of_pos hi1 (hypos i1)
      linarith
    have hvj : ∀ j : S, m * y j ≤ v j := by
      intro j
      have := hi0 j (Finset.mem_univ _)
      rw [le_div_iff₀ (hypos j)] at this
      exact this
    have hle : (P *ᵥ v) i0 ≤ m * (P *ᵥ y) i0 := by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = i0
      · subst hj
        have : v j = m * y j := by
          rw [hm]; field_simp [(hypos j).ne']
        rw [this]; ring_nf; exact le_refl _
      · have hoffj : P i0 j ≤ 0 := hoff _ _ (fun h => hj (Subtype.ext h.symm))
        calc P i0 j * v j ≤ P i0 j * (m * y j) :=
              mul_le_mul_of_nonpos_left (hvj j) hoffj
          _ = m * (P i0 j * y j) := by ring
    have := hPy i0
    have := hv i0
    nlinarith
  have hinj : Function.Injective P.mulVec := by
    intro v w hvw
    have h1 : P *ᵥ (v - w) = 0 := by rw [Matrix.mulVec_sub, hvw, sub_self]
    have h2 : ∀ i, 0 ≤ v i - w i := key (v - w) (by rw [h1]; intro i; simp)
    have h3 : ∀ i, 0 ≤ -(v i - w i) := by
      have := key (-(v - w)) (by rw [Matrix.mulVec_neg, h1]; intro i; simp)
      intro i; simpa using this i
    funext i
    linarith [h2 i, h3 i]
  have hunit : IsUnit P.det := by
    rw [← Matrix.isUnit_iff_isUnit_det]
    exact Matrix.mulVec_injective_iff_isUnit.mp hinj
  refine ⟨hunit, ?_⟩
  intro i j
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hunit
  have := key (fun k => P⁻¹ k j) (by
    intro k
    have : (P *ᵥ fun k => P⁻¹ k j) k = (P * P⁻¹) k j := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [this, hPP, Matrix.one_apply]
    split_ifs <;> norm_num)
  exact this i

theorem solution {n : ℕ} (M K : Matrix (Fin n) (Fin n) ℝ) (hM : PDASNewton.Perturb.IsMMatrix M)
    (S : Finset (Fin n)) (hA : IsUnit (PDASNewton.MMatrix.principal (M + K) S).det) :
    ∀ i j, ((PDASNewton.MMatrix.principal (M + K) S)⁻¹ * PDASNewton.MMatrix.offDiag (M + K) S) i j ≤
      ((PDASNewton.MMatrix.principal M S)⁻¹ * PDASNewton.MMatrix.offDiag K S -
        (PDASNewton.MMatrix.principal M S)⁻¹ * PDASNewton.MMatrix.principal K S * (PDASNewton.MMatrix.principal (M + K) S)⁻¹ * PDASNewton.MMatrix.offDiag (M + K) S) i j := by
  obtain ⟨hMu, hNn⟩ := pdp_principal_Mmat M hM S
  set MI := PDASNewton.MMatrix.principal M S with hMI
  set KI := PDASNewton.MMatrix.principal K S with hKI
  set MIA := PDASNewton.MMatrix.offDiag M S with hMIA
  set KIA := PDASNewton.MMatrix.offDiag K S with hKIA
  have hAI : PDASNewton.MMatrix.principal (M + K) S = MI + KI := by
    ext i j; simp [PDASNewton.MMatrix.principal, hMI, hKI]
  have hAIA : PDASNewton.MMatrix.offDiag (M + K) S = MIA + KIA := by
    ext i j; simp [PDASNewton.MMatrix.offDiag, hMIA, hKIA]
  rw [hAI] at hA ⊢
  rw [hAIA]
  set U := (MI + KI)⁻¹ with hU
  set N := MI⁻¹ with hN
  have hNM : N * MI = 1 := Matrix.nonsing_inv_mul MI hMu
  have hAU : (MI + KI) * U = 1 := Matrix.mul_nonsing_inv _ hA
  have hUe : U = N - N * KI * U := by
    have : MI * U = 1 - KI * U := by
      have := hAU
      rw [add_mul] at this
      rw [← this]; abel
    calc U = (N * MI) * U := by rw [hNM, one_mul]
      _ = N * (MI * U) := by rw [Matrix.mul_assoc]
      _ = N - N * KI * U := by rw [this, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  have hid : U * (MIA + KIA) = (N * KIA - N * KI * U * (MIA + KIA)) + N * MIA := by
    calc U * (MIA + KIA) = (N - N * KI * U) * (MIA + KIA) := by rw [← hUe]
      _ = _ := by
        rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add]
        simp only [Matrix.mul_assoc]
        abel
  intro i j
  rw [hid]
  have hnp : (N * MIA) i j ≤ 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_nonpos
    intro k _
    have h1 : 0 ≤ N i k := hNn i k
    have h2 : MIA k j ≤ 0 := by
      simp only [hMIA, PDASNewton.MMatrix.offDiag, Matrix.submatrix_apply]
      apply hM.2.1
      intro h
      have hk : (k : Fin n) ∈ S := k.2
      have hj : (j : Fin n) ∈ Sᶜ := j.2
      rw [h] at hk
      exact (Finset.mem_compl.mp hj) hk
    exact mul_nonpos_of_nonneg_of_nonpos h1 h2
  rw [Matrix.add_apply]
  linarith
