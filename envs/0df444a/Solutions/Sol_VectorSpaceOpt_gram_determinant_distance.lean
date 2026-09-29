-- Prove2me | solution 1 for VectorSpaceOpt.gram_determinant_distance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T15:06:47.648017+00:00
-- url     : https://prove2.me/submissions/628d6d38-1376-488e-8669-490ea008e59c

import Mathlib
open scoped RealInnerProductSpace

/-- Gram matrices transform by congruence under a linear change of family. -/
theorem vsm_gram_conj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (z : Fin m → H) :
    Matrix.gram ℝ (fun i => ∑ k, A i k • z k) = A * Matrix.gram ℝ z * A.transpose := by
  ext i j
  have hL : (⟪∑ k, A i k • z k, ∑ l, A j l • z l⟫ : ℝ)
      = ∑ k, ∑ l, A i k * ⟪z k, z l⟫ * A j l := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [real_inner_smul_right]; ring
  have hR : (A * Matrix.gram ℝ z * A.transpose) i j
      = ∑ l, ∑ k, A i k * ⟪z k, z l⟫ * A j l := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.gram_apply, Finset.sum_mul]
  show (⟪∑ k, A i k • z k, ∑ l, A j l • z l⟫ : ℝ) = _
  rw [hL, hR, Finset.sum_comm]


theorem solution {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (y : Fin n → H) (hy : LinearIndependent ℝ y)
    (x : H) :
    (⨅ m : Submodule.span ℝ (Set.range y), ‖x - (m : H)‖) ^ 2 =
      (Matrix.of fun i j : Fin (n + 1) => ⟪(Fin.snoc y x : Fin (n + 1) → H) i, (Fin.snoc y x : Fin (n + 1) → H) j⟫).det /
      (Matrix.of fun i j : Fin n => ⟪y i, y j⟫).det := by
  classical
  set M : Submodule ℝ H := Submodule.span ℝ (Set.range y) with hMdef
  haveI hfd : FiniteDimensional ℝ M := by
    rw [hMdef]; exact FiniteDimensional.span_of_finite ℝ (Set.finite_range y)
  haveI : CompleteSpace M := FiniteDimensional.complete ℝ M
  obtain ⟨p, hpe⟩ : ∃ p, p = M.starProjection x := ⟨_, rfl⟩
  obtain ⟨e, hee⟩ : ∃ e, e = x - p := ⟨_, rfl⟩
  have hpMem : p ∈ M := by rw [hpe]; exact M.starProjection_apply_mem x
  have heorth : ∀ w ∈ M, ⟪e, w⟫ = (0:ℝ) := by
    intro w hw
    have h1 : x - M.starProjection x ∈ Mᗮ := M.sub_starProjection_mem_orthogonal x
    have h2 : ⟪w, x - M.starProjection x⟫ = (0:ℝ) := (Submodule.mem_orthogonal M _).1 h1 w hw
    rw [hee, hpe, real_inner_comm]
    exact h2
  have hinf : (⨅ m : M, ‖x - (m : H)‖) = ‖e‖ := by
    have hmin := (M.norm_eq_iInf_iff_real_inner_eq_zero hpMem).2
      (fun w hw => by rw [← hee]; exact heorth w hw)
    rw [hee]
    exact hmin.symm
  obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, ∑ i, c i • y i = p :=
    (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).1 (by rw [← hMdef]; exact hpMem)
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      A = Matrix.of fun i j => if i = Fin.last n then (Fin.snoc c (1:ℝ)) j
        else (if i = j then (1:ℝ) else 0) := ⟨_, rfl⟩
  have hkey : ∀ i : Fin (n + 1),
      ∑ k, A i k • (Fin.snoc y e : Fin (n + 1) → H) k = (Fin.snoc y x : Fin (n + 1) → H) i := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i₀, rfl⟩ | rfl
    · have hne : (Fin.castSucc i₀) ≠ Fin.last n := (Fin.castSucc_lt_last i₀).ne
      have hAc : ∀ k, A (Fin.castSucc i₀) k = (if Fin.castSucc i₀ = k then (1:ℝ) else 0) := by
        intro k; rw [hA]; simp only [Matrix.of_apply, if_neg hne]
      simp only [hAc, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        Fin.snoc_castSucc]
    · have hAl : ∀ k, A (Fin.last n) k = (Fin.snoc c (1:ℝ) : Fin (n+1) → ℝ) k := by
        intro k; rw [hA]; simp
      simp only [hAl]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_last, Fin.snoc_castSucc, one_smul]
      rw [hc, hee]
      abel
  have hAtdet : (A.transpose).det = 1 := by
    have htri : (A.transpose).BlockTriangular id := by
      intro i j hij
      have hjl : j ≠ Fin.last n := by
        intro hc2
        rw [hc2] at hij
        exact absurd (Fin.le_last i) (not_le.2 hij)
      have hji : j ≠ i := ne_of_lt hij
      rw [Matrix.transpose_apply, hA]
      simp [hjl, hji]
    rw [Matrix.det_of_upperTriangular htri]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [Matrix.transpose_apply, hA]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i₀, rfl⟩ | rfl
    · simp [(Fin.castSucc_lt_last i₀).ne]
    · simp
  have hAdet : A.det = 1 := by rw [← Matrix.det_transpose A]; exact hAtdet
  have hgram : Matrix.gram ℝ (Fin.snoc y x : Fin (n + 1) → H)
      = A * Matrix.gram ℝ (Fin.snoc y e : Fin (n + 1) → H) * A.transpose := by
    have hfun : (fun i => ∑ k, A i k • (Fin.snoc y e : Fin (n + 1) → H) k)
        = (Fin.snoc y x : Fin (n + 1) → H) := funext hkey
    rw [← hfun, vsm_gram_conj]
  have hdet1 : (Matrix.gram ℝ (Fin.snoc y x : Fin (n + 1) → H)).det
      = (Matrix.gram ℝ (Fin.snoc y e : Fin (n + 1) → H)).det := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hAdet]
    ring
  have hsub : (Matrix.gram ℝ (Fin.snoc y e : Fin (n + 1) → H)).submatrix
      (Fin.succAbove (Fin.last n)) (Fin.succAbove (Fin.last n)) = Matrix.gram ℝ y := by
    rw [Fin.succAbove_last]
    ext i j
    simp [Matrix.gram_apply]
  have hdet2 : (Matrix.gram ℝ (Fin.snoc y e : Fin (n + 1) → H)).det
      = ⟪e, e⟫ * (Matrix.gram ℝ y).det := by
    rw [Matrix.det_succ_column _ (Fin.last n)]
    rw [Finset.sum_eq_single (Fin.last n)]
    · rw [hsub]
      have hpow : ((-1 : ℝ)) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) = 1 := by
        simp only [Fin.val_last]
        exact Even.neg_one_pow ⟨n, rfl⟩
      rw [hpow, one_mul]
      congr 1
      simp [Matrix.gram_apply]
    · intro b _ hb
      obtain ⟨b₀, rfl⟩ : ∃ b₀ : Fin n, Fin.castSucc b₀ = b := by
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b₀, hb₀⟩ | hbl
        · exact ⟨b₀, hb₀.symm⟩
        · exact absurd hbl hb
      have hz : (Matrix.gram ℝ (Fin.snoc y e : Fin (n + 1) → H)) (Fin.castSucc b₀) (Fin.last n)
          = 0 := by
        show (⟪(Fin.snoc y e : Fin (n + 1) → H) (Fin.castSucc b₀),
          (Fin.snoc y e : Fin (n + 1) → H) (Fin.last n)⟫ : ℝ) = 0
        rw [Fin.snoc_castSucc, Fin.snoc_last, real_inner_comm]
        exact heorth (y b₀) (by rw [hMdef]; exact Submodule.subset_span ⟨b₀, rfl⟩)
      rw [hz, mul_zero, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ (Fin.last n)) hcon
  have hy0 : (Matrix.gram ℝ y).det ≠ 0 :=
    Matrix.det_gram_ne_zero_iff_linearIndependent.2 hy
  have hL : (Matrix.of fun i j : Fin (n + 1) =>
      ⟪(Fin.snoc y x : Fin (n + 1) → H) i, (Fin.snoc y x : Fin (n + 1) → H) j⟫)
      = Matrix.gram ℝ (Fin.snoc y x : Fin (n + 1) → H) := rfl
  have hR : (Matrix.of fun i j : Fin n => ⟪y i, y j⟫) = Matrix.gram ℝ y := rfl
  rw [hL, hR, hdet1, hdet2, hinf, mul_div_assoc, div_self hy0, mul_one,
    real_inner_self_eq_norm_sq]
