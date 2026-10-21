-- Prove2me | solution 1 for PDASNewton.Perturb.g_estimate
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:45:46.883779+00:00
-- url     : https://prove2.me/submissions/82e1cec6-7b57-4eba-98c6-88e0a1281106

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


namespace PDPAux

lemma colsum_le {m p : Type*} [Fintype m] [Fintype p] (B : Matrix m p ℝ) (j : p) :
    ∑ i, |B i j| ≤ PDASNewton.Perturb.oneNorm B := by
  unfold PDASNewton.Perturb.oneNorm
  have h1 : ((∑ i, |B i j|).toNNReal : NNReal) ≤
      Finset.univ.sup (fun j : p => (∑ i, |B i j|).toNNReal) :=
    Finset.le_sup (f := fun j : p => (∑ i, |B i j|).toNNReal) (Finset.mem_univ j)
  have h2 : (((∑ i, |B i j|).toNNReal : NNReal) : ℝ) ≤
      ((Finset.univ.sup fun j : p => (∑ i, |B i j|).toNNReal : NNReal) : ℝ) := by
    exact_mod_cast h1
  rw [Real.coe_toNNReal _ (Finset.sum_nonneg (fun i _ => abs_nonneg _))] at h2
  exact h2

lemma oneNorm_nonneg {m p : Type*} [Fintype m] [Fintype p] (B : Matrix m p ℝ) :
    0 ≤ PDASNewton.Perturb.oneNorm B := NNReal.coe_nonneg _

lemma l1_mulVec {m p : Type*} [Fintype m] [Fintype p] (B : Matrix m p ℝ) (g : p → ℝ) :
    ∑ i, |(B *ᵥ g) i| ≤ PDASNewton.Perturb.oneNorm B * ∑ j, |g j| := by
  calc ∑ i, |(B *ᵥ g) i| ≤ ∑ i, ∑ j, |B i j| * |g j| := by
        apply Finset.sum_le_sum
        intro i _
        simp only [Matrix.mulVec, dotProduct]
        calc |∑ j, B i j * g j| ≤ ∑ j, |B i j * g j| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j, |B i j| * |g j| := by simp [abs_mul]
    _ = ∑ j, (∑ i, |B i j|) * |g j| := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
    _ ≤ ∑ j, PDASNewton.Perturb.oneNorm B * |g j| :=
        Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_right (colsum_le B j) (abs_nonneg _))
    _ = _ := by rw [Finset.mul_sum]

lemma principal_add {n : ℕ} (M K : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    PDASNewton.MMatrix.principal (M + K) S =
      PDASNewton.MMatrix.principal M S + PDASNewton.MMatrix.principal K S := by
  ext i j
  simp [PDASNewton.MMatrix.principal]

lemma setup {n : ℕ} (M K : Matrix (Fin n) (Fin n) ℝ) (hM : PDASNewton.Perturb.IsMMatrix M)
    (ρ : ℝ) (hρ : ∀ S : Finset (Fin n), PDASNewton.Perturb.oneNorm
      ((PDASNewton.MMatrix.principal M S)⁻¹ * PDASNewton.MMatrix.principal K S) ≤ ρ)
    (hρ_half : ρ < 1 / 2) (S : Finset (Fin n)) :
    0 ≤ ρ ∧
    IsUnit (1 + (PDASNewton.MMatrix.principal M S)⁻¹ * PDASNewton.MMatrix.principal K S).det ∧
    IsUnit (PDASNewton.MMatrix.principal (M + K) S).det ∧
    (PDASNewton.MMatrix.principal (M + K) S)⁻¹ =
      (1 + (PDASNewton.MMatrix.principal M S)⁻¹ * PDASNewton.MMatrix.principal K S)⁻¹ *
        (PDASNewton.MMatrix.principal M S)⁻¹ := by
  obtain ⟨hPu, hNn⟩ := pdp_principal_Mmat M hM S
  set P := PDASNewton.MMatrix.principal M S with hP
  set Q := PDASNewton.MMatrix.principal K S with hQ
  set B := P⁻¹ * Q with hB
  have hρS : PDASNewton.Perturb.oneNorm B ≤ ρ := hρ S
  have hρ0 : 0 ≤ ρ := (oneNorm_nonneg B).trans hρS
  have hPN : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have hAeq : P + Q = P * (1 + B) := by
    rw [Matrix.mul_add, Matrix.mul_one, hB, ← Matrix.mul_assoc, hPN, Matrix.one_mul]
  have hB1 : ∀ g : S → ℝ, ∑ i, |(B *ᵥ g) i| ≤ ρ * ∑ j, |g j| := fun g =>
    (l1_mulVec B g).trans (mul_le_mul_of_nonneg_right hρS (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
  have hinj : Function.Injective (1 + B).mulVec := by
    intro a b hab
    set g := a - b with hg
    have hz : (1 + B) *ᵥ g = 0 := by
      rw [hg, Matrix.mulVec_sub, hab, sub_self]
    have hz' : g + B *ᵥ g = 0 := by
      rwa [Matrix.add_mulVec, Matrix.one_mulVec] at hz
    have hgi : ∀ i, g i = -(B *ᵥ g) i := by
      intro i
      have := congrFun hz' i
      simp only [Pi.add_apply, Pi.zero_apply] at this
      linarith
    have hs : ∑ i, |g i| ≤ ρ * ∑ i, |g i| := by
      calc ∑ i, |g i| = ∑ i, |(B *ᵥ g) i| := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hgi i, abs_neg]
        _ ≤ ρ * ∑ i, |g i| := hB1 g
    have hnn : 0 ≤ ∑ i, |g i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have h0 : ∑ i, |g i| ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    have h00 : ∑ i, |g i| = 0 := le_antisymm h0 hnn
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg (g i))).mp h00
    funext i
    have hi := this i (Finset.mem_univ i)
    have : g i = 0 := abs_eq_zero.mp hi
    have : a i - b i = 0 := this
    linarith
  have hU : IsUnit (1 + B).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  have hAu : IsUnit (P + Q).det := by
    rw [hAeq, Matrix.det_mul]; exact hPu.mul hU
  refine ⟨hρ0, hU, ?_, ?_⟩
  · rw [PDPAux.principal_add]; exact hAu
  · rw [PDPAux.principal_add, hAeq, Matrix.mul_inv_rev]

end PDPAux

theorem solution {n : ℕ} (M K : Matrix (Fin n) (Fin n) ℝ) (hM : PDASNewton.Perturb.IsMMatrix M)
    (ρ : ℝ) (hρ : ∀ S : Finset (Fin n), PDASNewton.Perturb.oneNorm ((PDASNewton.MMatrix.principal M S)⁻¹ * PDASNewton.MMatrix.principal K S) ≤ ρ)
    (hρ_half : ρ < 1 / 2) :
    ∀ (S : Finset (Fin n)) (v : S → ℝ), v ≤ 0 →
      (1 - 2 * ρ) / (1 - ρ) * ∑ i, |((PDASNewton.MMatrix.principal M S)⁻¹ *ᵥ v) i| ≤
        ∑ i, (-((PDASNewton.MMatrix.principal (M + K) S)⁻¹ *ᵥ v)) i := by
  intro S v hv
  obtain ⟨hρ0, hU, hAu, hAinv⟩ := PDPAux.setup M K hM ρ hρ hρ_half S
  obtain ⟨hPu, hNn⟩ := pdp_principal_Mmat M hM S
  set P := PDASNewton.MMatrix.principal M S with hP
  set Q := PDASNewton.MMatrix.principal K S with hQ
  set N := P⁻¹ with hN
  set B := N * Q with hB
  set U := (1 + B)⁻¹ with hUdef
  have hρS : PDASNewton.Perturb.oneNorm B ≤ ρ := hρ S
  have hUU : (1 + B) * U = 1 := Matrix.mul_nonsing_inv _ hU
  have hB1 : ∀ g : S → ℝ, ∑ i, |(B *ᵥ g) i| ≤ ρ * ∑ j, |g j| := fun g =>
    (PDPAux.l1_mulVec B g).trans
      (mul_le_mul_of_nonneg_right hρS (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
  -- the vector w = -(N v) is nonnegative
  set w : S → ℝ := fun i => -(N *ᵥ v) i with hw
  have hNv : ∀ i, (N *ᵥ v) i ≤ 0 := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_nonpos
    intro j _
    exact mul_nonpos_of_nonneg_of_nonpos (hNn i j) (hv j)
  have hw0 : ∀ i, 0 ≤ w i := fun i => by simp only [hw]; linarith [hNv i]
  have habs : ∀ i, |(N *ᵥ v) i| = w i := fun i => by
    rw [abs_of_nonpos (hNv i)]
  set g : S → ℝ := fun i => (-((PDASNewton.MMatrix.principal (M + K) S)⁻¹ *ᵥ v)) i with hg
  have hgU : g = U *ᵥ w := by
    funext i
    simp only [hg, hAinv, ← Matrix.mulVec_mulVec, Pi.neg_apply]
    have hw' : w = -(N *ᵥ v) := rfl
    rw [hw', Matrix.mulVec_neg]
    rfl
  have hgw : g + B *ᵥ g = w := by
    have : (1 + B) *ᵥ g = w := by
      rw [hgU, Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
    rwa [Matrix.add_mulVec, Matrix.one_mulVec] at this
  have hgi : ∀ i, g i = w i - (B *ᵥ g) i := fun i => by
    have := congrFun hgw i
    simp only [Pi.add_apply] at this
    linarith
  set W := ∑ i, w i with hWdef
  have hWabs : ∑ i, |(N *ᵥ v) i| = W := Finset.sum_congr rfl (fun i _ => habs i)
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun i _ => hw0 i)
  -- sum bounds
  have h1 : W - ρ * ∑ i, |g i| ≤ ∑ i, g i := by
    have : ∑ i, g i = W - ∑ i, (B *ᵥ g) i := by
      rw [hWdef, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => hgi i)
    have h2 : ∑ i, (B *ᵥ g) i ≤ ∑ i, |(B *ᵥ g) i| :=
      Finset.sum_le_sum (fun i _ => le_abs_self _)
    have := hB1 g
    linarith
  have h2 : (1 - ρ) * ∑ i, |g i| ≤ W := by
    have h3 : ∑ i, |g i| ≤ W + ∑ i, |(B *ᵥ g) i| := by
      calc ∑ i, |g i| ≤ ∑ i, (w i + |(B *ᵥ g) i|) := by
            apply Finset.sum_le_sum
            intro i _
            rw [hgi i]
            calc |w i - (B *ᵥ g) i| ≤ |w i| + |(B *ᵥ g) i| := abs_sub _ _
              _ = w i + |(B *ᵥ g) i| := by rw [abs_of_nonneg (hw0 i)]
        _ = W + ∑ i, |(B *ᵥ g) i| := by rw [Finset.sum_add_distrib]
    have := hB1 g
    nlinarith
  have hρ1 : 0 < 1 - ρ := by linarith
  rw [hWabs, div_mul_eq_mul_div, div_le_iff₀ hρ1]
  have hG0 : 0 ≤ ∑ i, |g i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hsum : ∑ i, (-((PDASNewton.MMatrix.principal (M + K) S)⁻¹ *ᵥ v)) i = ∑ i, g i := rfl
  rw [hsum]
  nlinarith [mul_nonneg hρ1.le (sub_nonneg.mpr h1), mul_nonneg hρ0 (sub_nonneg.mpr h2)]
