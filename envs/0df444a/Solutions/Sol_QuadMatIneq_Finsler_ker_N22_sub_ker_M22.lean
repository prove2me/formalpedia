-- Prove2me | solution 1 for QuadMatIneq.Finsler.ker_N22_sub_ker_M22
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:33:35.056734+00:00
-- url     : https://prove2.me/submissions/b51e0ff8-37c1-47ab-b204-25fa38555364

import Mathlib
import Definitions.Def_QuadMatIneq_Finsler_QMI

set_option autoImplicit false
open Matrix QuadMatIneq.Basic QuadMatIneq.Finsler

section QMFPrelude
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem qmf_mp_unique (A : Matrix m n ℝ) (X Y : Matrix n m ℝ)
    (hX : IsMoorePenrose A X) (hY : IsMoorePenrose A Y) : X = Y := by
  obtain ⟨hX1, hX2, hX3, hX4⟩ := hX
  obtain ⟨hY1, hY2, hY3, hY4⟩ := hY
  have h1 : A * X = A * Y := by
    calc A * X = (A * Y * A) * X := by rw [hY1]
      _ = (A * Y) * (A * X) := by simp only [Matrix.mul_assoc]
      _ = (A * Y)ᵀ * (A * X)ᵀ := by rw [hY3, hX3]
      _ = (A * X * A * Y)ᵀ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (A * Y)ᵀ := by rw [hX1]
      _ = A * Y := hY3
  have h2 : X * A = Y * A := by
    calc X * A = X * (A * Y * A) := by rw [hY1]
      _ = (X * A) * (Y * A) := by simp only [Matrix.mul_assoc]
      _ = (X * A)ᵀ * (Y * A)ᵀ := by rw [hY4, hX4]
      _ = (Y * A * X * A)ᵀ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (Y * A)ᵀ := by
          have : Y * A * (X * A) = Y * A := by
            calc Y * A * (X * A) = Y * (A * X * A) := by simp only [Matrix.mul_assoc]
              _ = Y * A := by rw [hX1]
          simp only [Matrix.mul_assoc] at this ⊢
          rw [this]
      _ = Y * A := hY4
  calc X = X * A * X := hX2.symm
    _ = Y * A * X := by rw [h2]
    _ = Y * (A * X) := by rw [Matrix.mul_assoc]
    _ = Y * (A * Y) := by rw [h1]
    _ = Y * A * Y := by rw [Matrix.mul_assoc]
    _ = Y := hY2

theorem qmf_conj_transpose (U X : Matrix n n ℝ) : (U * X * Uᵀ)ᵀ = U * Xᵀ * Uᵀ := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem qmf_mp_conj (U D E : Matrix n n ℝ) (h1 : U * Uᵀ = 1) (h2 : Uᵀ * U = 1)
    (hD : IsMoorePenrose D E) : IsMoorePenrose (U * D * Uᵀ) (U * E * Uᵀ) := by
  obtain ⟨p1, p2, p3, p4⟩ := hD
  have h2' : ∀ Y : Matrix n n ℝ, Uᵀ * (U * Y) = Y := by
    intro Y; rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have e1 : U * D * Uᵀ * (U * E * Uᵀ) = U * (D * E) * Uᵀ := by
    simp only [Matrix.mul_assoc, h2']
  have e2 : U * E * Uᵀ * (U * D * Uᵀ) = U * (E * D) * Uᵀ := by
    simp only [Matrix.mul_assoc, h2']
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc U * D * Uᵀ * (U * E * Uᵀ) * (U * D * Uᵀ) = U * (D * E * D) * Uᵀ := by
          simp only [Matrix.mul_assoc, h2']
      _ = U * D * Uᵀ := by rw [p1]
  · calc U * E * Uᵀ * (U * D * Uᵀ) * (U * E * Uᵀ) = U * (E * D * E) * Uᵀ := by
          simp only [Matrix.mul_assoc, h2']
      _ = U * E * Uᵀ := by rw [p2]
  · rw [e1, qmf_conj_transpose, p3]
  · rw [e2, qmf_conj_transpose, p4]

theorem qmf_mp_diag (l : n → ℝ) :
    IsMoorePenrose (diagonal l) (diagonal (fun i => (l i)⁻¹)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; by_cases h : l i = 0 <;> simp [h]
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; by_cases h : l i = 0 <;> simp [h]
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_transpose]
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_transpose]

theorem qmf_mp_exists_symm (A : Matrix n n ℝ) (hA : Aᵀ = A) : ∃ X, IsMoorePenrose A X := by
  have hH : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hA
  set U : Matrix n n ℝ := (hH.eigenvectorUnitary : Matrix n n ℝ) with hU
  set l : n → ℝ := hH.eigenvalues with hl
  have hUU : U * Uᵀ = 1 := by
    have := (Unitary.mem_iff.mp hH.eigenvectorUnitary.2).2
    simpa [hU, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hUU' : Uᵀ * U = 1 := by
    have := (Unitary.mem_iff.mp hH.eigenvectorUnitary.2).1
    simpa [hU, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hAeq : A = U * diagonal l * Uᵀ := by
    have := hH.spectral_theorem
    rw [this]
    simp [hU, hl, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  refine ⟨U * diagonal (fun i => (l i)⁻¹) * Uᵀ, ?_⟩
  rw [hAeq]
  exact qmf_mp_conj U _ _ hUU hUU' (qmf_mp_diag l)

theorem qmf_pinv_spec (A : Matrix n n ℝ) (hA : Aᵀ = A) : IsMoorePenrose A (pinv A) :=
  Classical.epsilon_spec (qmf_mp_exists_symm A hA)

theorem qmf_pinv_symm (A : Matrix n n ℝ) (hA : Aᵀ = A) : (pinv A)ᵀ = pinv A := by
  have h := qmf_pinv_spec A hA
  obtain ⟨p1, p2, p3, p4⟩ := h
  apply qmf_mp_unique A
  · refine ⟨?_, ?_, ?_, ?_⟩
    · have := congrArg Matrix.transpose p1
      simpa [Matrix.transpose_mul, hA, Matrix.mul_assoc] using this
    · have := congrArg Matrix.transpose p2
      simpa [Matrix.transpose_mul, hA, Matrix.mul_assoc] using this
    · have := congrArg Matrix.transpose p4
      simp only [Matrix.transpose_mul, hA, Matrix.transpose_transpose] at this
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, hA]
      exact this
    · have := congrArg Matrix.transpose p3
      simp only [Matrix.transpose_mul, hA, Matrix.transpose_transpose] at this
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, hA]
      exact this
  · exact qmf_pinv_spec A hA

end QMFPrelude
section QMFPrelude2
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem qmf_qmiForm (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (Z : Matrix κ ι ℝ) :
    qmiForm P Z = P.toBlocks₁₁ + P.toBlocks₁₂ * Z + Zᵀ * P.toBlocks₂₁ + Zᵀ * P.toBlocks₂₂ * Z := by
  unfold qmiForm
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks P]
  rw [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

theorem qmf_cong (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (Z : Matrix κ ι ℝ) :
    (Matrix.fromBlocks (1 : Matrix ι ι ℝ) 0 Z 1)ᵀ * P * Matrix.fromBlocks 1 0 Z 1 =
      Matrix.fromBlocks (qmiForm P Z) (P.toBlocks₁₂ + Zᵀ * P.toBlocks₂₂)
        (P.toBlocks₂₁ + P.toBlocks₂₂ * Z) P.toBlocks₂₂ := by
  rw [qmf_qmiForm]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks P]
  simp only [Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
    Matrix.fromBlocks_multiply]
  congr 1 <;> simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc] <;> abel

end QMFPrelude2
section QMFPrelude3
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem qmf_mat_zero {p q : Type*} [Fintype q] [DecidableEq q] (M : Matrix p q ℝ)
    (h : ∀ v : q → ℝ, M *ᵥ v = 0) : M = 0 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa using this

theorem qmf_ker_mul {p : Type*} (A : Matrix κ κ ℝ) (hA : Aᵀ = A) (B : Matrix p κ ℝ)
    (hker : ∀ v : κ → ℝ, A *ᵥ v = 0 → B *ᵥ v = 0) : B * (pinv A * A) = B := by
  have hspec := qmf_pinv_spec A hA
  have hAC : A * (1 - pinv A * A) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hspec.1, sub_self]
  have h0 : B * (1 - pinv A * A) = 0 := by
    apply qmf_mat_zero
    intro v
    rw [← Matrix.mulVec_mulVec]
    apply hker
    rw [Matrix.mulVec_mulVec, hAC, Matrix.zero_mulVec]
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h0
  exact h0.symm

theorem qmf_blocks_symm (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : Pᵀ = P) :
    P.toBlocks₁₁ᵀ = P.toBlocks₁₁ ∧ P.toBlocks₁₂ᵀ = P.toBlocks₂₁ ∧ P.toBlocks₂₁ᵀ = P.toBlocks₁₂ ∧
      P.toBlocks₂₂ᵀ = P.toBlocks₂₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    have := congrFun (congrFun hP (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.toBlocks₁₁] using this
  · ext i j
    have := congrFun (congrFun hP (Sum.inr i)) (Sum.inl j)
    simpa [Matrix.toBlocks₁₂, Matrix.toBlocks₂₁] using this
  · ext i j
    have := congrFun (congrFun hP (Sum.inl i)) (Sum.inr j)
    simpa [Matrix.toBlocks₁₂, Matrix.toBlocks₂₁] using this
  · ext i j
    have := congrFun (congrFun hP (Sum.inr i)) (Sum.inr j)
    simpa [Matrix.toBlocks₂₂] using this

theorem qmf_herm_T (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (h : P.IsHermitian) : Pᵀ = P := by
  have := h.eq
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

end QMFPrelude3
section QMFPrelude4
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem qmf_ker_left {p q : Type*} (A : Matrix κ κ ℝ) (hA : Aᵀ = A) (B : Matrix p κ ℝ)
    (hker : ∀ v : κ → ℝ, A *ᵥ v = 0 → B *ᵥ v = 0) :
    (∀ W : Matrix κ q ℝ, B * (pinv A * (A * W)) = B * W) ∧ A * (pinv A * Bᵀ) = Bᵀ := by
  have hk := qmf_ker_mul A hA B hker
  have hspec := qmf_pinv_spec A hA
  have hXs := qmf_pinv_symm A hA
  have hXN : (pinv A * A)ᵀ = pinv A * A := hspec.2.2.2
  refine ⟨fun W => ?_, ?_⟩
  · rw [← Matrix.mul_assoc (pinv A), ← Matrix.mul_assoc, hk]
  · have hcomm : A * pinv A = pinv A * A := by
      have := hXN
      rw [Matrix.transpose_mul, hXs, hA] at this
      exact this
    have := congrArg Matrix.transpose hk
    rw [Matrix.transpose_mul, hXN] at this
    rw [← Matrix.mul_assoc, hcomm]
    exact this

theorem qmf_pinv_idem (A : Matrix κ κ ℝ) (hA : Aᵀ = A) {q : Type*} (W : Matrix κ q ℝ) :
    pinv A * (A * (pinv A * W)) = pinv A * W := by
  have := (qmf_pinv_spec A hA).2.1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, this]

end QMFPrelude4
theorem qmf_eq_4_7 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hMh : M.IsHermitian) (hNh : N.IsHermitian)
    (hMker : ∀ v : κ → ℝ, M.toBlocks₂₂ *ᵥ v = 0 → M.toBlocks₁₂ *ᵥ v = 0) :
    Theta M N = schur M +
      (pinv M.toBlocks₂₂ * M.toBlocks₂₁ - pinv N.toBlocks₂₂ * N.toBlocks₂₁)ᵀ * M.toBlocks₂₂ *
        (pinv M.toBlocks₂₂ * M.toBlocks₂₁ - pinv N.toBlocks₂₂ * N.toBlocks₂₁) ∧
    M.toBlocks₂₂ * (pinv M.toBlocks₂₂ * M.toBlocks₂₁ - pinv N.toBlocks₂₂ * N.toBlocks₂₁) =
      M.toBlocks₂₁ - M.toBlocks₂₂ * pinv N.toBlocks₂₂ * N.toBlocks₂₁ := by
  obtain ⟨-, hM12, hM21, hM22⟩ := qmf_blocks_symm M (qmf_herm_T M hMh)
  obtain ⟨-, hN12, hN21, hN22⟩ := qmf_blocks_symm N (qmf_herm_T N hNh)
  have hYs := qmf_pinv_symm M.toBlocks₂₂ hM22
  have hXs := qmf_pinv_symm N.toBlocks₂₂ hN22
  obtain ⟨ga, gb⟩ := qmf_ker_left (q := ι) M.toBlocks₂₂ hM22 M.toBlocks₁₂ hMker
  rw [hM12] at gb
  have hcomm : M.toBlocks₂₂ * pinv M.toBlocks₂₂ = pinv M.toBlocks₂₂ * M.toBlocks₂₂ := by
    have := (qmf_pinv_spec M.toBlocks₂₂ hM22).2.2.2
    rw [Matrix.transpose_mul, hYs, hM22] at this
    exact this
  refine ⟨?_, ?_⟩
  · unfold Theta schur
    rw [qmf_qmiForm]
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_neg, hYs, hXs, hM21, hN21]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc,
      neg_neg, ga, gb]
    abel
  · simp only [Matrix.mul_sub, Matrix.mul_assoc, gb]

section QMFPrelude5
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem qmf_qmiN (N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hN : InPi N) (hNs : schur N = 0) :
    qmiForm N (-pinv N.toBlocks₂₂ * N.toBlocks₂₁) = 0 := by
  obtain ⟨hNh, -, -, hkerN⟩ := hN
  obtain ⟨-, hN12, hN21, hN22⟩ := qmf_blocks_symm N (qmf_herm_T N hNh)
  have hXs := qmf_pinv_symm N.toBlocks₂₂ hN22
  obtain ⟨ga, -⟩ := qmf_ker_left (q := ι) N.toBlocks₂₂ hN22 N.toBlocks₁₂ hkerN
  have e : N.toBlocks₁₁ = N.toBlocks₁₂ * (pinv N.toBlocks₂₂ * N.toBlocks₂₁) := by
    have := hNs; unfold schur at this
    rw [← Matrix.mul_assoc]
    exact sub_eq_zero.mp this
  rw [qmf_qmiForm]
  simp only [Matrix.transpose_mul, Matrix.transpose_neg, hXs, hN21, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.mul_assoc, neg_neg, ga]
  rw [e]
  abel

end QMFPrelude5

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Nonempty ι]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hM : InPi M) (hN : InPi N) (hNs : schur N = 0)
    (hsub : ZZero N ⊆ ZSet M) :
    ∀ v : κ → ℝ, N.toBlocks₂₂ *ᵥ v = 0 → M.toBlocks₂₂ *ᵥ v = 0 := by
  intro v hv
  have hZ0 : (-pinv N.toBlocks₂₂ * N.toBlocks₂₁) ∈ ZZero N := qmf_qmiN N hN hNs
  obtain ⟨hMh, hMneg, -, -⟩ := hM
  obtain ⟨hNh, -, -, hkerN⟩ := hN
  have hN12v : N.toBlocks₁₂ *ᵥ v = 0 := hkerN v hv
  obtain ⟨-, hN12, hN21, hN22⟩ := qmf_blocks_symm N (qmf_herm_T N hNh)
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  set e : ι → ℝ := Pi.single i₀ 1 with he
  set Z0 : Matrix κ ι ℝ := -pinv N.toBlocks₂₂ * N.toBlocks₂₁ with hZ0def
  set R : Matrix κ ι ℝ := Matrix.vecMulVec v e with hR
  have hR1 : N.toBlocks₁₂ * R = 0 := by
    rw [hR, Matrix.mul_vecMulVec, hN12v]; ext; simp [Matrix.vecMulVec]
  have hR2 : N.toBlocks₂₂ * R = 0 := by
    rw [hR, Matrix.mul_vecMulVec, hv]; ext; simp [Matrix.vecMulVec]
  have hRt : Rᵀ = Matrix.vecMulVec e v := by rw [hR, Matrix.transpose_vecMulVec]
  have hR3 : Rᵀ * N.toBlocks₂₁ = 0 := by
    rw [hRt, Matrix.vecMulVec_mul]
    have : v ᵥ* N.toBlocks₂₁ = 0 := by rw [← hN12, Matrix.vecMul_transpose, hN12v]
    rw [this]; ext; simp [Matrix.vecMulVec]
  have hR4 : Rᵀ * N.toBlocks₂₂ = 0 := by
    rw [hRt, Matrix.vecMulVec_mul]
    have : v ᵥ* N.toBlocks₂₂ = 0 := by
      rw [← hN22, Matrix.vecMul_transpose]; exact hv
    rw [this]; ext; simp [Matrix.vecMulVec]
  have hR4' : ∀ W : Matrix κ ι ℝ, Rᵀ * (N.toBlocks₂₂ * W) = 0 := fun W => by
    rw [← Matrix.mul_assoc, hR4, Matrix.zero_mul]
  have hA : ∀ t : ℝ, (Z0 + t • R) ∈ ZZero N := by
    intro t
    have h0 : qmiForm N Z0 = 0 := hZ0
    show qmiForm N (Z0 + t • R) = 0
    rw [qmf_qmiForm] at h0 ⊢
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hR1, hR2, hR3, hR4, hR4',
      Matrix.mul_zero, Matrix.zero_mul, smul_zero, add_zero, zero_add] at h0 ⊢
    exact h0
  have hpos : ∀ t : ℝ, 0 ≤ e ⬝ᵥ (qmiForm M (Z0 + t • R) *ᵥ e) := by
    intro t
    have := (hsub (hA t)).dotProduct_mulVec_nonneg e
    simpa using this
  -- the quadratic form as a polynomial in t
  set y0 : ι ⊕ κ → ℝ := Sum.elim e (Z0 *ᵥ e) with hy0
  set yv : ι ⊕ κ → ℝ := Sum.elim (0 : ι → ℝ) v with hyv
  have hee : e ⬝ᵥ e = 1 := by simp [he]
  have hform : ∀ t : ℝ, e ⬝ᵥ (qmiForm M (Z0 + t • R) *ᵥ e) = (y0 + t • yv) ⬝ᵥ (M *ᵥ (y0 + t • yv)) := by
    intro t
    have hy : Matrix.fromRows (1 : Matrix ι ι ℝ) (Z0 + t • R) *ᵥ e = y0 + t • yv := by
      rw [Matrix.fromRows_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, hR, Matrix.vecMulVec_mulVec,
        hee]
      ext (i | i) <;> simp [hy0, hyv]
    unfold qmiForm
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, hy]
  have hc : yv ⬝ᵥ (M *ᵥ yv) = v ⬝ᵥ (M.toBlocks₂₂ *ᵥ v) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [Matrix.fromBlocks_mulVec]
    simp [hyv, dotProduct, Fintype.sum_sum_type]
  set A : ℝ := y0 ⬝ᵥ (M *ᵥ y0) with hAdef
  set B : ℝ := y0 ⬝ᵥ (M *ᵥ yv) + yv ⬝ᵥ (M *ᵥ y0) with hBdef
  set c : ℝ := v ⬝ᵥ (M.toBlocks₂₂ *ᵥ v) with hcdef
  have hq : ∀ t : ℝ, 0 ≤ A + B * t + c * t ^ 2 := by
    intro t
    have h1 := hpos t
    rw [hform] at h1
    have : (y0 + t • yv) ⬝ᵥ (M *ᵥ (y0 + t • yv)) = A + B * t + c * t ^ 2 := by
      rw [← hc]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul, hAdef, hBdef]
      ring
    linarith
  have hc0 : 0 ≤ c := by
    by_contra hneg
    push_neg at hneg
    have hA0 : 0 ≤ A := by simpa using hq 0
    set s : ℝ := Real.sqrt ((A + 1) / (-c)) with hs
    have hs2 : s ^ 2 = (A + 1) / (-c) := Real.sq_sqrt (by apply div_nonneg <;> linarith)
    have h1 := hq s
    have h2 := hq (-s)
    have hcne : c ≠ 0 := hneg.ne
    have h3 : c * s ^ 2 = -(A + 1) := by
      rw [hs2]; field_simp
    nlinarith
  have hcle : c ≤ 0 := by
    have := hMneg.dotProduct_mulVec_nonneg v
    rw [Matrix.neg_mulVec, dotProduct_neg] at this
    simp only [star_trivial] at this
    linarith
  have hczero : star v ⬝ᵥ ((-M.toBlocks₂₂) *ᵥ v) = 0 := by
    rw [Matrix.neg_mulVec, dotProduct_neg, star_trivial]
    have : c = 0 := le_antisymm hcle hc0
    rw [hcdef] at this
    rw [this]; simp
  have := (hMneg.dotProduct_mulVec_zero_iff v).mp hczero
  rwa [Matrix.neg_mulVec, neg_eq_zero] at this
