-- Prove2me | solution 1 for QuadMatIneq.Basic.nonempty_iff_schur_psd
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:06:51.443531+00:00
-- url     : https://prove2.me/submissions/4b703fe9-cb67-455c-96aa-3a317b7c41ff

import Mathlib
import Definitions.Def_QuadMatIneq_Basic_QMI

set_option autoImplicit false
open Matrix QuadMatIneq.Basic

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

section QMBMain
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem qmb_key (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : P.IsHermitian)
    (hker : ∀ v : κ → ℝ, P.toBlocks₂₂ *ᵥ v = 0 → P.toBlocks₁₂ *ᵥ v = 0) (Z : Matrix κ ι ℝ) :
    schur P - qmiForm P Z =
      (Z + pinv P.toBlocks₂₂ * P.toBlocks₂₁)ᵀ * (-P.toBlocks₂₂) *
        (Z + pinv P.toBlocks₂₂ * P.toBlocks₂₁) := by
  obtain ⟨h11, h12, h21, hD⟩ := qmf_blocks_symm P (qmf_herm_T P hP)
  have hXs := qmf_pinv_symm P.toBlocks₂₂ hD
  obtain ⟨ga, gb⟩ := qmf_ker_left (q := ι) P.toBlocks₂₂ hD P.toBlocks₁₂ hker
  have gc := qmf_ker_mul P.toBlocks₂₂ hD P.toBlocks₁₂ hker
  rw [h12] at gb
  rw [qmf_qmiForm]
  unfold schur
  simp only [Matrix.transpose_add, Matrix.transpose_mul, hXs, h21, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, gb, ga]
  have gc' : P.toBlocks₁₂ * (pinv P.toBlocks₂₂ * (P.toBlocks₂₂ * Z)) = P.toBlocks₁₂ * Z := ga Z
  abel

theorem qmb_main (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : P.IsHermitian)
    (h22 : (-P.toBlocks₂₂).PosSemidef)
    (hker : ∀ v : κ → ℝ, P.toBlocks₂₂ *ᵥ v = 0 → P.toBlocks₁₂ *ᵥ v = 0) :
    schur P = qmiForm P (-(pinv P.toBlocks₂₂ * P.toBlocks₂₁)) ∧
      ∀ Z : Matrix κ ι ℝ, (schur P - qmiForm P Z).PosSemidef := by
  refine ⟨?_, fun Z => ?_⟩
  · have := qmb_key P hP hker (-(pinv P.toBlocks₂₂ * P.toBlocks₂₁))
    rw [neg_add_cancel, Matrix.transpose_zero, Matrix.zero_mul, Matrix.zero_mul] at this
    exact (sub_eq_zero.mp this)
  · rw [qmb_key P hP hker Z]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      h22.conjTranspose_mul_mul_same (Z + pinv P.toBlocks₂₂ * P.toBlocks₂₁)

end QMBMain

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : P.IsHermitian) (h22 : (-P.toBlocks₂₂).PosSemidef)
    (hker : ∀ v : κ → ℝ, P.toBlocks₂₂ *ᵥ v = 0 → P.toBlocks₁₂ *ᵥ v = 0) :
    (ZSet P).Nonempty ↔ (schur P).PosSemidef := by
  obtain ⟨h1, h2⟩ := qmb_main P hP h22 hker
  constructor
  · rintro ⟨Z, hZ⟩
    have := (h2 Z).add hZ
    simpa using this
  · intro h
    refine ⟨-(pinv P.toBlocks₂₂ * P.toBlocks₂₁), ?_⟩
    show (qmiForm P _).PosSemidef
    rw [← h1]; exact h
