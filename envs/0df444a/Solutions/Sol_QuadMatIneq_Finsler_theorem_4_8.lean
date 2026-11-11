-- Prove2me | solution 1 for QuadMatIneq.Finsler.theorem_4_8
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T14:50:55.796452+00:00
-- url     : https://prove2.me/submissions/500eb17d-1d59-489d-973c-1fd4fe4b158b

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Definitions.Def_QuadMatIneq_Finsler_QMI
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.NormNum

-- Inlined component: P080Support

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


 theorem qmf_ker_N22_sub_ker_M22 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Nonempty ι]
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

 theorem qmf_eq_4_6 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hMh : M.IsHermitian) (hN : InPi N) (hNs : schur N = 0) :
    (Tmat N)ᵀ * N * Tmat N = Matrix.fromBlocks 0 0 0 N.toBlocks₂₂ ∧
    (Tmat N)ᵀ * M * Tmat N =
      Matrix.fromBlocks (Theta M N)
        (M.toBlocks₁₂ - N.toBlocks₁₂ * pinv N.toBlocks₂₂ * M.toBlocks₂₂)
        (M.toBlocks₂₁ - M.toBlocks₂₂ * pinv N.toBlocks₂₂ * N.toBlocks₂₁)
        M.toBlocks₂₂ ∧
    ∀ α : ℝ, (Tmat N)ᵀ * (M - α • N) * Tmat N =
      Matrix.fromBlocks (Theta M N)
        (M.toBlocks₁₂ - N.toBlocks₁₂ * pinv N.toBlocks₂₂ * M.toBlocks₂₂)
        (M.toBlocks₂₁ - M.toBlocks₂₂ * pinv N.toBlocks₂₂ * N.toBlocks₂₁)
        (M.toBlocks₂₂ - α • N.toBlocks₂₂) := by
  obtain ⟨hNh, -, -, hkerN⟩ := hN
  have hNT := qmf_herm_T N hNh
  obtain ⟨-, hN12, hN21, hN22⟩ := qmf_blocks_symm N hNT
  have hspec := qmf_pinv_spec N.toBlocks₂₂ hN22
  have hXs := qmf_pinv_symm N.toBlocks₂₂ hN22
  have hk12 := qmf_ker_mul N.toBlocks₂₂ hN22 N.toBlocks₁₂ hkerN
  set X := pinv N.toBlocks₂₂ with hX
  set Z : Matrix κ ι ℝ := -X * N.toBlocks₂₁ with hZ
  have hXN : (X * N.toBlocks₂₂)ᵀ = X * N.toBlocks₂₂ := hspec.2.2.2
  have hZt : Zᵀ = -(N.toBlocks₁₂ * X) := by
    rw [hZ, Matrix.transpose_mul, Matrix.transpose_neg, hXs, hN21, Matrix.mul_neg]
  have hcomm : N.toBlocks₂₂ * X = X * N.toBlocks₂₂ := by
    have := hXN
    rw [Matrix.transpose_mul, hXs, hN22] at this
    exact this
  have hk21' : (X * N.toBlocks₂₂) * N.toBlocks₂₁ = N.toBlocks₂₁ := by
    have := congrArg Matrix.transpose hk12
    rw [Matrix.transpose_mul, hXN, hN12] at this
    exact this
  have hk21 : N.toBlocks₂₂ * (X * N.toBlocks₂₁) = N.toBlocks₂₁ := by
    rw [← Matrix.mul_assoc, hcomm, hk21']
  have g12 : ∀ Y : Matrix κ ι ℝ, N.toBlocks₁₂ * (X * (N.toBlocks₂₂ * Y)) = N.toBlocks₁₂ * Y := by
    intro Y
    rw [← Matrix.mul_assoc X, ← Matrix.mul_assoc, hk12]
  have hT : Tmat N = Matrix.fromBlocks 1 0 Z 1 := rfl
  have hA : (Tmat N)ᵀ * N * Tmat N = Matrix.fromBlocks 0 0 0 N.toBlocks₂₂ := by
    rw [hT, qmf_cong]
    congr 1
    · rw [qmf_qmiForm, hZt, hZ]
      have e : N.toBlocks₁₁ = N.toBlocks₁₂ * (X * N.toBlocks₂₁) := by
        have := hNs; unfold schur at this
        rw [← Matrix.mul_assoc]
        exact sub_eq_zero.mp this
      simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
      rw [g12 (X * N.toBlocks₂₁), e]
      abel
    · rw [hZt, Matrix.neg_mul, Matrix.mul_assoc, ← sub_eq_add_neg, sub_eq_zero]; exact (hk12).symm
    · rw [hZ]
      simp only [Matrix.neg_mul, Matrix.mul_neg, hk21]
      abel
  have hB : (Tmat N)ᵀ * M * Tmat N =
      Matrix.fromBlocks (Theta M N)
        (M.toBlocks₁₂ - N.toBlocks₁₂ * X * M.toBlocks₂₂)
        (M.toBlocks₂₁ - M.toBlocks₂₂ * X * N.toBlocks₂₁)
        M.toBlocks₂₂ := by
    rw [hT, qmf_cong]
    congr 1
    · rw [hZt, Matrix.neg_mul, sub_eq_add_neg]
    · rw [hZ]
      simp only [Matrix.neg_mul, Matrix.mul_neg, sub_eq_add_neg, Matrix.mul_assoc]
  refine ⟨hA, hB, fun α => ?_⟩
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hB, hA]
  change _ = Matrix.fromBlocks (Theta M N) (M.toBlocks₁₂ - N.toBlocks₁₂ * X * M.toBlocks₂₂)
    (M.toBlocks₂₁ - M.toBlocks₂₂ * X * N.toBlocks₂₁) (M.toBlocks₂₂ - α • N.toBlocks₂₂)
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

 theorem qmf_theta_psd_ker_schur {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hM : InPi M) (hN : InPi N) (hNs : schur N = 0)
    (hsub : ZZero N ⊆ ZSet M) :
    (Theta M N).PosSemidef ∧
    ∀ v : ι → ℝ, schur M *ᵥ v = 0 ↔
      (Theta M N *ᵥ v = 0 ∧
        (M.toBlocks₂₁ - M.toBlocks₂₂ * pinv N.toBlocks₂₂ * N.toBlocks₂₁) *ᵥ v = 0) := by
  have hZ0 : (-pinv N.toBlocks₂₂ * N.toBlocks₂₁) ∈ ZZero N := qmf_qmiN N hN hNs
  have hΘ : (Theta M N).PosSemidef := hsub hZ0
  obtain ⟨hMh, hMneg, -, hMker⟩ := hM
  have hNh := hN.1
  obtain ⟨h47a, h47b⟩ := qmf_eq_4_7 M N hMh hNh hMker
  set D : Matrix κ ι ℝ := pinv M.toBlocks₂₂ * M.toBlocks₂₁ - pinv N.toBlocks₂₂ * N.toBlocks₂₁ with hD
  refine ⟨hΘ, fun v => ?_⟩
  have hΘv : Theta M N *ᵥ v = schur M *ᵥ v + Dᵀ *ᵥ (M.toBlocks₂₂ *ᵥ (D *ᵥ v)) := by
    rw [h47a, Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hBv : (M.toBlocks₂₁ - M.toBlocks₂₂ * pinv N.toBlocks₂₂ * N.toBlocks₂₁) *ᵥ v
      = M.toBlocks₂₂ *ᵥ (D *ᵥ v) := by
    rw [← h47b, Matrix.mulVec_mulVec]
  rw [hBv]
  constructor
  · intro hv
    have h1 : v ⬝ᵥ (Theta M N *ᵥ v) = (D *ᵥ v) ⬝ᵥ (M.toBlocks₂₂ *ᵥ (D *ᵥ v)) := by
      rw [hΘv, hv, zero_add, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have h2 : 0 ≤ v ⬝ᵥ (Theta M N *ᵥ v) := by
      simpa using hΘ.dotProduct_mulVec_nonneg v
    have h3 : 0 ≤ (D *ᵥ v) ⬝ᵥ ((-M.toBlocks₂₂) *ᵥ (D *ᵥ v)) := by
      simpa using hMneg.dotProduct_mulVec_nonneg (D *ᵥ v)
    rw [Matrix.neg_mulVec, dotProduct_neg] at h3
    have h4 : star (D *ᵥ v) ⬝ᵥ ((-M.toBlocks₂₂) *ᵥ (D *ᵥ v)) = 0 := by
      rw [Matrix.neg_mulVec, dotProduct_neg, star_trivial]
      linarith
    have h5 := (hMneg.dotProduct_mulVec_zero_iff (D *ᵥ v)).mp h4
    rw [Matrix.neg_mulVec, neg_eq_zero] at h5
    refine ⟨?_, h5⟩
    rw [hΘv, hv, h5, Matrix.mulVec_zero, zero_add]
  · rintro ⟨h1, h2⟩
    rw [hΘv, h2, Matrix.mulVec_zero] at h1
    simpa using h1


-- Inlined component: P080Schur

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Matrix QuadMatIneq.Basic QuadMatIneq.Finsler

namespace S13Schur

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A block matrix is a sum of two positive congruences once the off-diagonal
block factors through the top block. This form also covers singular A. -/
theorem block_posSemidef_of_factor (A : Matrix ι ι ℝ) (B : Matrix κ ι ℝ)
    (C : Matrix κ κ ℝ) (X : Matrix ι κ ℝ) (hA : A.PosSemidef)
    (hAX : A * X = Bᵀ) (hXA : Xᵀ * A = B)
    (hS : (C - B * X).PosSemidef) :
    (Matrix.fromBlocks A Bᵀ B C).PosSemidef := by
  have hgram : (Matrix.fromBlocks A Bᵀ B (B * X)).PosSemidef := by
    have h := hA.conjTranspose_mul_mul_same (Matrix.fromCols (1 : Matrix ι ι ℝ) X)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_fromCols, Matrix.transpose_one, Matrix.fromRows_mul] at h
    simpa only [Matrix.one_mul, hXA, Matrix.fromRows_mul_fromCols,
      Matrix.mul_one, hAX] using h
  have htail : (Matrix.fromBlocks (0 : Matrix ι ι ℝ) (0 : Matrix ι κ ℝ)
      (0 : Matrix κ ι ℝ) (C - B * X)).PosSemidef := by
    have h := hS.conjTranspose_mul_mul_same
      (Matrix.fromCols (0 : Matrix κ ι ℝ) (1 : Matrix κ κ ℝ))
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_fromCols, Matrix.transpose_zero, Matrix.transpose_one,
      Matrix.fromRows_mul] at h
    simpa only [Matrix.zero_mul, Matrix.one_mul,
      Matrix.fromRows_mul_fromCols, Matrix.mul_zero, Matrix.mul_one] using h
  have hsum := hgram.add htail
  simpa only [Matrix.fromBlocks_add, add_zero, ← add_sub_assoc,
    add_sub_cancel_left] using hsum

/-- The sufficient generalized Schur criterion with its essential kernel
condition. The pseudo-inverse is the unchanged published epsilon definition. -/
theorem schur_sufficient (A : Matrix ι ι ℝ) (B : Matrix κ ι ℝ)
    (C : Matrix κ κ ℝ) (hA : A.PosSemidef)
    (hker : ∀ v : ι → ℝ, A *ᵥ v = 0 → B *ᵥ v = 0)
    (hS : (C - B * pinv A * Bᵀ).PosSemidef) :
    (Matrix.fromBlocks A Bᵀ B C).PosSemidef := by
  have hAT : Aᵀ = A := by
    have h := hA.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hPs : (pinv A)ᵀ = pinv A := qmf_pinv_symm A hAT
  have hBA := qmf_ker_mul A hAT B hker
  have hAB := (qmf_ker_left (q := κ) A hAT B hker).2
  apply block_posSemidef_of_factor A B C (pinv A * Bᵀ) hA hAB
  · simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hPs,
      Matrix.mul_assoc] using hBA
  · simpa only [Matrix.mul_assoc] using hS

/-- A right inverse suffices to pull positive semidefiniteness back through a
matrix congruence. -/
theorem posSemidef_of_congruence {m : Type*} [Fintype m] [DecidableEq m]
    (P T U : Matrix m m ℝ) (hTU : T * U = 1)
    (hP : (Tᵀ * P * T).PosSemidef) : P.PosSemidef := by
  have h := hP.conjTranspose_mul_mul_same U
  have heq : Uᵀ * (Tᵀ * P * T) * U = P := by
    calc
      Uᵀ * (Tᵀ * P * T) * U = (T * U)ᵀ * P * (T * U) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = P := by rw [hTU]; simp
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, heq] using h

/-- The triangular congruence in the original Finsler definition preserves
positive semidefiniteness in both directions, including empty block types. -/
theorem tmat_posSemidef_iff (P N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    ((Tmat N)ᵀ * P * Tmat N).PosSemidef ↔ P.PosSemidef := by
  let Z : Matrix κ ι ℝ := -(pinv N.toBlocks₂₂) * N.toBlocks₂₁
  let U : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := Matrix.fromBlocks 1 0 (-Z) 1
  have hTU : Tmat N * U = 1 := by
    change Matrix.fromBlocks (1 : Matrix ι ι ℝ) 0 Z (1 : Matrix κ κ ℝ) *
      Matrix.fromBlocks 1 0 (-Z) 1 = 1
    simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
      Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, add_neg_cancel,
      Matrix.fromBlocks_one]
  constructor
  · exact posSemidef_of_congruence P (Tmat N) U hTU
  · intro hP
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hP.conjTranspose_mul_mul_same (Tmat N)


end S13Schur

-- Inlined component: P080Domination

set_option autoImplicit false

open Matrix

namespace S13Domination

lemma scalar_product_bound (r a b : ℝ) :
    r * a * b ≤ |r| * (a ^ 2 + b ^ 2) / 2 := by
  by_cases hr : 0 ≤ r
  · rw [abs_of_nonneg hr]
    nlinarith only [mul_nonneg hr (sq_nonneg (a - b))]
  · rw [abs_of_neg (lt_of_not_ge hr)]
    have hn : 0 ≤ -r := neg_nonneg.mpr (le_of_not_ge hr)
    nlinarith only [mul_nonneg hn (sq_nonneg (a + b))]

/-- A symmetric quadratic form is bounded by its absolute row sums. -/
lemma row_sum_bound {n : Type*} [Fintype n] (B : Matrix n n ℝ)
    (hB : Bᵀ = B) (x : n → ℝ) :
    x ⬝ᵥ (B *ᵥ x) ≤ ∑ i, (∑ j, |B i j|) * x i ^ 2 := by
  have hs (i j : n) : B i j = B j i := congrFun (congrFun hB j) i
  have hrow : (∑ i, ∑ j, |B i j| * x i ^ 2) =
      ∑ i, (∑ j, |B i j|) * x i ^ 2 := by
    simp only [Finset.sum_mul]
  have hcol : (∑ i, ∑ j, |B i j| * x j ^ 2) =
      ∑ i, (∑ j, |B i j|) * x i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    calc
      (∑ i, |B i j| * x j ^ 2) = ∑ i, |B j i| * x j ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hs i j]
      _ = (∑ i, |B j i|) * x j ^ 2 := (Finset.sum_mul _ _ _).symm
  calc
    x ⬝ᵥ (B *ᵥ x) = ∑ i, ∑ j, B i j * x i * x j := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ ∑ i, ∑ j, |B i j| * (x i ^ 2 + x j ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact scalar_product_bound _ _ _
    _ = ∑ i, (∑ j, |B i j|) * x i ^ 2 := by
      simp_rw [mul_add, add_div, Finset.sum_add_distrib, ← Finset.sum_div]
      rw [hrow, hcol]
      ring

/-- Diagonal domination, including zero diagonal entries and an empty index type. -/
lemma diagonal_domination {n : Type*} [Fintype n] [DecidableEq n]
    (l : n → ℝ) (hl : ∀ i, 0 ≤ l i) (B : Matrix n n ℝ) (hB : Bᵀ = B)
    (hker : ∀ v : n → ℝ, diagonal l *ᵥ v = 0 → B *ᵥ v = 0) :
    ∃ α : ℝ, 0 ≤ α ∧ (α • diagonal l - B).PosSemidef := by
  let r := fun i => ∑ j, |B i j|
  let α := ∑ i, r i / l i
  have hr (i : n) : 0 ≤ r i := Finset.sum_nonneg fun j hj => abs_nonneg _
  have hratio (i : n) : 0 ≤ r i / l i := div_nonneg (hr i) (hl i)
  have ha : 0 ≤ α := Finset.sum_nonneg fun i hi => hratio i
  have hs (i j : n) : B i j = B j i := congrFun (congrFun hB j) i
  have hr0 (i : n) (hi : l i = 0) : r i = 0 := by
    have hdi : diagonal l *ᵥ Pi.single i 1 = 0 := by
      simp [Matrix.diagonal_mulVec_single, hi]
    have hz := hker (Pi.single i 1) hdi
    have hcol (j : n) : B j i = 0 := by
      have h := congrFun hz j
      simpa using h
    apply Finset.sum_eq_zero
    intro j hj
    rw [hs i j, hcol j, abs_zero]
  have hrow (i : n) : r i ≤ α * l i := by
    by_cases hi : l i = 0
    · simp [hr0 i hi, hi]
    · have hip : 0 < l i := lt_of_le_of_ne (hl i) (Ne.symm hi)
      have hle : r i / l i ≤ α :=
        Finset.single_le_sum (fun j hj => hratio j) (Finset.mem_univ i)
      exact (div_le_iff₀ hip).mp hle
  have hquad (x : n → ℝ) : x ⬝ᵥ (B *ᵥ x) ≤ α * (x ⬝ᵥ (diagonal l *ᵥ x)) := by
    calc
      x ⬝ᵥ (B *ᵥ x) ≤ ∑ i, r i * x i ^ 2 := row_sum_bound B hB x
      _ ≤ ∑ i, (α * l i) * x i ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
      _ = α * (x ⬝ᵥ (diagonal l *ᵥ x)) := by
        simp only [dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  refine ⟨α, ha, Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    simp [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.diagonal_transpose, hB]
  · intro x
    have h := sub_nonneg.mpr (hquad x)
    simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
      star_trivial] using h

/-- A symmetric form that kills the kernel of a positive semidefinite form is
bounded above by a nonnegative scalar multiple of that form. -/
theorem exists_dominating_smul {n : Type*} [Fintype n] [DecidableEq n]
    (H G : Matrix n n ℝ) (hH : H.PosSemidef) (hG : Gᵀ = G)
    (hker : ∀ v : n → ℝ, H *ᵥ v = 0 → G *ᵥ v = 0) :
    ∃ α : ℝ, 0 ≤ α ∧ (α • H - G).PosSemidef := by
  let U : Matrix n n ℝ := (hH.isHermitian.eigenvectorUnitary : Matrix n n ℝ)
  let l : n → ℝ := hH.isHermitian.eigenvalues
  have hl (i : n) : 0 ≤ l i := hH.eigenvalues_nonneg i
  have hUU : U * Uᵀ = 1 := by
    have h := (Unitary.mem_iff.mp hH.isHermitian.eigenvectorUnitary.2).2
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hUU' : Uᵀ * U = 1 := by
    have h := (Unitary.mem_iff.mp hH.isHermitian.eigenvectorUnitary.2).1
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hHspec : H = U * diagonal l * Uᵀ := by
    have h := hH.isHermitian.spectral_theorem
    rw [h]
    simp [U, l, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  let B := Uᵀ * G * U
  have hB : Bᵀ = B := by
    simp [B, Matrix.transpose_mul, hG, Matrix.mul_assoc]
  have hHU : H * U = U * diagonal l := by
    rw [hHspec]
    simp [Matrix.mul_assoc, hUU']
  have hkerB : ∀ v : n → ℝ, diagonal l *ᵥ v = 0 → B *ᵥ v = 0 := by
    intro v hv
    have hHv : H *ᵥ (U *ᵥ v) = 0 := by
      rw [Matrix.mulVec_mulVec, hHU, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    have hGv := hker (U *ᵥ v) hHv
    dsimp [B]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGv, Matrix.mulVec_zero]
  obtain ⟨α, ha, hpsd⟩ := diagonal_domination l hl B hB hkerB
  have hBconj : U * B * Uᵀ = G := by
    dsimp [B]
    calc
      U * (Uᵀ * G * U) * Uᵀ = (U * Uᵀ) * G * (U * Uᵀ) := by
        simp only [Matrix.mul_assoc]
      _ = G := by rw [hUU]; simp
  have hconj : U * (α • diagonal l - B) * Uᵀ = α • H - G := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hBconj, ← hHspec]
  refine ⟨α, ha, ?_⟩
  have h := hpsd.mul_mul_conjTranspose_same U
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hconj] using h

end S13Domination


-- Inlined component: P080

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Matrix QuadMatIneq.Basic QuadMatIneq.Finsler

namespace S13Finsler

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Every multiplier, of either sign, gives the required zero-set inclusion. -/
theorem multiplier_sufficient (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (h : ∃ α : ℝ, (M - α • N).PosSemidef) : ZZero N ⊆ ZSet M := by
  obtain ⟨α, hα⟩ := h
  intro Z hZ
  change qmiForm N Z = 0 at hZ
  change (qmiForm M Z).PosSemidef
  have hcong := hα.conjTranspose_mul_mul_same
    (Matrix.fromRows (1 : Matrix ι ι ℝ) Z)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hcong
  change (qmiForm (M - α • N) Z).PosSemidef at hcong
  have heq : qmiForm (M - α • N) Z = qmiForm M Z - α • qmiForm N Z := by
    simp only [qmiForm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  rwa [heq, hZ, smul_zero, sub_zero] at hcong

end S13Finsler

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hMh : M.IsHermitian) (hNh : N.IsHermitian) :
    ((∃ α : ℝ, (M - α • N).PosSemidef) → ZZero N ⊆ ZSet M) ∧
    (Nonempty ι → InPi M → InPi N → schur N = 0 →
      (∀ v : ι → ℝ, Theta M N *ᵥ v = 0 → schur M *ᵥ v = 0) →
      (ZZero N ⊆ ZSet M ↔ ∃ α : ℝ, 0 ≤ α ∧ (M - α • N).PosSemidef)) := by
  have hsuff := S13Finsler.multiplier_sufficient M N
  refine ⟨hsuff, ?_⟩
  intro hι hM hN hNs hker
  letI : Nonempty ι := hι
  constructor
  · intro hsub
    let A : Matrix ι ι ℝ := Theta M N
    let B : Matrix κ ι ℝ :=
      M.toBlocks₂₁ - M.toBlocks₂₂ * pinv N.toBlocks₂₂ * N.toBlocks₂₁
    let H : Matrix κ κ ℝ := -N.toBlocks₂₂
    let G : Matrix κ κ ℝ := -M.toBlocks₂₂ + B * pinv A * Bᵀ
    have htheta := qmf_theta_psd_ker_schur M N hM hN hNs hsub
    have hA : A.PosSemidef := htheta.1
    have hBA : ∀ v : ι → ℝ, A *ᵥ v = 0 → B *ᵥ v = 0 := by
      intro v hv
      exact ((htheta.2 v).mp (hker v hv)).2
    have hNM := qmf_ker_N22_sub_ker_M22 M N hM hN hNs hsub
    obtain ⟨_, _, hM21, hM22⟩ := qmf_blocks_symm M (qmf_herm_T M hMh)
    obtain ⟨_, _, hN21, hN22⟩ := qmf_blocks_symm N (qmf_herm_T N hNh)
    have hPinvN := qmf_pinv_symm N.toBlocks₂₂ hN22
    have hBT : Bᵀ =
        M.toBlocks₁₂ - N.toBlocks₁₂ * pinv N.toBlocks₂₂ * M.toBlocks₂₂ := by
      simp only [B, Matrix.transpose_sub, Matrix.transpose_mul, hM21, hN21,
        hM22, hPinvN, Matrix.mul_assoc]
    have hAT : Aᵀ = A := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
    have hPinvA := qmf_pinv_symm A hAT
    have hG : Gᵀ = G := by
      simp only [G, Matrix.transpose_add, Matrix.transpose_neg, hM22,
        Matrix.transpose_mul, Matrix.transpose_transpose, hPinvA, Matrix.mul_assoc]
    have hH : H.PosSemidef := hN.2.1
    have hHG : ∀ v : κ → ℝ, H *ᵥ v = 0 → G *ᵥ v = 0 := by
      intro v hv
      have hNv : N.toBlocks₂₂ *ᵥ v = 0 := by
        simpa only [H, Matrix.neg_mulVec, neg_eq_zero] using hv
      have hMv : M.toBlocks₂₂ *ᵥ v = 0 := hNM v hNv
      have hM12v : M.toBlocks₁₂ *ᵥ v = 0 := hM.2.2.2 v hMv
      have hBtv : Bᵀ *ᵥ v = 0 := by
        rw [hBT]
        simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hMv,
          Matrix.mulVec_zero, hM12v, sub_self]
      simp only [G, Matrix.add_mulVec, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
        hMv, hBtv, Matrix.mulVec_zero, neg_zero, add_zero]
    obtain ⟨α, hα, hdom⟩ := S13Domination.exists_dominating_smul H G hH hG hHG
    have heq : α • H - G =
        (M.toBlocks₂₂ - α • N.toBlocks₂₂) - B * pinv A * Bᵀ := by
      dsimp [H, G]
      simp only [smul_neg]
      abel
    rw [heq] at hdom
    have hBlock := S13Schur.schur_sufficient A B
      (M.toBlocks₂₂ - α • N.toBlocks₂₂) hA hBA hdom
    rw [hBT] at hBlock
    refine ⟨α, hα, (S13Schur.tmat_posSemidef_iff (M - α • N) N).mp ?_⟩
    rw [(qmf_eq_4_6 M N hMh hN hNs).2.2 α]
    exact hBlock
  · rintro ⟨α, _, hα⟩
    exact hsuff ⟨α, hα⟩


#print axioms solution
