-- Prove2me | solution 1 for QuadMatIneq.Basic.theorem_3_2_e
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T01:43:20.556357+00:00
-- url     : https://prove2.me/submissions/2f5be57a-5b7f-41e9-9627-0af445c7530a

import Mathlib
import Definitions.Def_QuadMatIneq_Basic_QMI

open Matrix QuadMatIneq.Basic

namespace QMIAux

theorem spec_real {κ : Type*} [Fintype κ] [DecidableEq κ] (D : Matrix κ κ ℝ) (hD : D.IsHermitian) :
    ∃ U : Matrix κ κ ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ D = U * diagonal hD.eigenvalues * Uᵀ := by
  refine ⟨(hD.eigenvectorUnitary : Matrix κ κ ℝ), ?_, ?_, ?_⟩
  · have h := Unitary.coe_star_mul_self hD.eigenvectorUnitary
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  · have h := Unitary.coe_star_mul_self hD.eigenvectorUnitary
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
    exact mul_eq_one_comm.mp h
  · have h := hD.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    try rw [Unitary.coe_star] at h
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
    have e : (RCLike.ofReal ∘ hD.eigenvalues : κ → ℝ) = hD.eigenvalues := by
      ext i; simp
    rw [e] at h
    exact h

theorem exists_mp {κ : Type*} [Fintype κ] [DecidableEq κ] (D : Matrix κ κ ℝ)
    (hD : D.IsHermitian) : ∃ X, IsMoorePenrose D X := by
  obtain ⟨U, hU1, hU2, hDU⟩ := spec_real D hD
  generalize hD.eigenvalues = e at hDU
  have key : ∀ a b : Matrix κ κ ℝ, (U * a * Uᵀ) * (U * b * Uᵀ) = U * (a * b) * Uᵀ := by
    intro a b
    calc (U * a * Uᵀ) * (U * b * Uᵀ) = U * a * (Uᵀ * U) * b * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = U * (a * b) * Uᵀ := by rw [hU1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have tr : ∀ d : κ → ℝ, (U * diagonal d * Uᵀ)ᵀ = U * diagonal d * Uᵀ := by
    intro d
    rw [transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  have d1 : diagonal e * diagonal (fun i => (e i)⁻¹) * diagonal e = diagonal e := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; ext i
    by_cases h : e i = 0 <;> simp [h]
  have d2 : diagonal (fun i => (e i)⁻¹) * diagonal e * diagonal (fun i => (e i)⁻¹)
      = diagonal (fun i => (e i)⁻¹) := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; ext i
    by_cases h : e i = 0 <;> simp [h]
  subst hDU
  refine ⟨U * diagonal (fun i => (e i)⁻¹) * Uᵀ, ?_, ?_, ?_, ?_⟩
  · rw [key, key, d1]
  · rw [key, key, d2]
  · rw [key, diagonal_mul_diagonal, tr]
  · rw [key, diagonal_mul_diagonal, tr]

theorem pinv_spec {κ : Type*} [Fintype κ] [DecidableEq κ] (D : Matrix κ κ ℝ)
    (hD : D.IsHermitian) : IsMoorePenrose D (pinv D) := by
  unfold pinv
  exact Classical.epsilon_spec (exists_mp D hD)

theorem qmiForm_expand {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (Z : Matrix κ ι ℝ) :
    qmiForm P Z = P.toBlocks₁₁ + P.toBlocks₁₂ * Z + Zᵀ * P.toBlocks₂₁ + Zᵀ * P.toBlocks₂₂ * Z := by
  have h : qmiForm P Z = (fromRows (1 : Matrix ι ι ℝ) Z)ᵀ *
      (fromBlocks P.toBlocks₁₁ P.toBlocks₁₂ P.toBlocks₂₁ P.toBlocks₂₂ *
        fromRows (1 : Matrix ι ι ℝ) Z) := by
    rw [fromBlocks_toBlocks, ← Matrix.mul_assoc]; rfl
  rw [h, fromBlocks_mul_fromRows, transpose_fromRows, fromCols_mul_fromRows]
  simp only [Matrix.mul_one, transpose_one, Matrix.one_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel

theorem core {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (D X : Matrix κ κ ℝ) (hDt : Dᵀ = D)
    (h1 : D * X * D = D) (hker : ∀ v : κ → ℝ, D *ᵥ v = 0 → B *ᵥ v = 0) (Z : Matrix κ ι ℝ) :
    A + B * Z + Zᵀ * Bᵀ + Zᵀ * D * Z
      = A - B * X * Bᵀ + (Z + X * Bᵀ)ᵀ * D * (Z + X * Bᵀ) := by
  have hDX : D * (1 - X * D) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h1, sub_self]
  have hB0 : B * (1 - X * D) = 0 := by
    ext i j
    have hv : D *ᵥ (fun k => (1 - X * D) k j) = 0 := by
      ext i'
      have := congrFun (congrFun hDX i') j
      exact this
    have := congrFun (hker _ hv) i
    exact this
  have hE1 : B * (X * D) = B := by
    have := hB0
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  have hE3 : D * (Xᵀ * Bᵀ) = Bᵀ := by
    have := congrArg transpose hE1
    rw [transpose_mul, transpose_mul, hDt, Matrix.mul_assoc] at this
    exact this
  have hE4 : D * (X * Bᵀ) = Bᵀ := by
    calc D * (X * Bᵀ) = D * (X * (D * (Xᵀ * Bᵀ))) := by rw [hE3]
      _ = (D * X * D) * (Xᵀ * Bᵀ) := by simp only [Matrix.mul_assoc]
      _ = Bᵀ := by rw [h1, hE3]
  have hWD : (X * Bᵀ)ᵀ * D = B := by
    have := congrArg transpose hE4
    rw [transpose_mul, hDt, transpose_transpose] at this
    exact this
  have hWDM : ∀ M : Matrix κ ι ℝ, (X * Bᵀ)ᵀ * (D * M) = B * M := fun M => by
    rw [← Matrix.mul_assoc, hWD]
  have hWB : (X * Bᵀ)ᵀ * Bᵀ = B * (X * Bᵀ) :=
    (congrArg (fun M => (X * Bᵀ)ᵀ * M) hE4).symm.trans (hWDM _)
  rw [transpose_add]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hE4, hWDM, hWB]
  abel

theorem toBlocks₂₂_transpose {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hH : P.IsHermitian) :
    P.toBlocks₂₂ᵀ = P.toBlocks₂₂ := by
  ext i j
  have := hH.apply (Sum.inr i) (Sum.inr j)
  simpa [toBlocks₂₂] using this

theorem qmi_eq {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    ∃ W : Matrix κ ι ℝ, ∀ Z, qmiForm P Z
      = schur P + (Z + W)ᵀ * P.toBlocks₂₂ * (Z + W) := by
  obtain ⟨hH, -, -, hker⟩ := hP
  have hDt := toBlocks₂₂_transpose P hH
  have hC : P.toBlocks₂₁ = P.toBlocks₁₂ᵀ := by
    ext i j
    have := hH.apply (Sum.inl j) (Sum.inr i)
    simpa [toBlocks₂₁, toBlocks₁₂] using this
  have hDH : P.toBlocks₂₂.IsHermitian :=
    (conjTranspose_eq_transpose_of_trivial _).trans hDt
  obtain ⟨h1, -, -, -⟩ := pinv_spec _ hDH
  refine ⟨pinv P.toBlocks₂₂ * P.toBlocks₁₂ᵀ, fun Z => ?_⟩
  unfold schur
  rw [qmiForm_expand, hC]
  exact core _ _ _ _ hDt h1 hker Z

theorem quad_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (Y : Matrix κ ι ℝ) (D : Matrix κ κ ℝ)
    (x : ι → ℝ) : x ⬝ᵥ ((Yᵀ * D * Y) *ᵥ x) = (Y *ᵥ x) ⬝ᵥ (D *ᵥ (Y *ᵥ x)) := by
  rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x Yᵀ,
    vecMul_transpose]

theorem exists_conj {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (S : Matrix ι ι ℝ) (N : Matrix κ κ ℝ) (hS : S.PosSemidef) (hN : N.PosSemidef)
    (h : S.rank ≤ N.rank) : ∃ Y : Matrix κ ι ℝ, Yᵀ * N * Y = S := by
  obtain ⟨V, hV1, hV2, hSV⟩ := spec_real S hS.1
  obtain ⟨U, hU1, hU2, hNU⟩ := spec_real N hN.1
  have hs := hS.eigenvalues_nonneg
  have hn := hN.eigenvalues_nonneg
  rw [hS.1.rank_eq_card_non_zero_eigs, hN.1.rank_eq_card_non_zero_eigs] at h
  generalize hS.1.eigenvalues = s at *
  generalize hN.1.eigenvalues = n at *
  obtain ⟨σ⟩ := Function.Embedding.nonempty_of_card_le h
  let M : Matrix κ ι ℝ := fun i j =>
    if hj : s j ≠ 0 then (if (σ ⟨j, hj⟩ : κ) = i then Real.sqrt (s j / n i) else 0) else 0
  have hM : Mᵀ * diagonal n * M = diagonal s := by
    ext j k
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    by_cases hj : s j ≠ 0
    · rw [Finset.sum_eq_single (σ ⟨j, hj⟩ : κ)]
      · have hMj : M (σ ⟨j, hj⟩) j = Real.sqrt (s j / n (σ ⟨j, hj⟩)) := by simp [M, hj]
        by_cases hjk : j = k
        · rw [← hjk, hMj, diagonal_apply_eq]
          have hn0 : n (σ ⟨j, hj⟩) ≠ 0 := (σ ⟨j, hj⟩).2
          have hnn := hn (σ ⟨j, hj⟩)
          have h0 : 0 ≤ s j / n (σ ⟨j, hj⟩) := div_nonneg (hs j) hnn
          have e := Real.mul_self_sqrt h0
          have e2 : s j / n (σ ⟨j, hj⟩) * n (σ ⟨j, hj⟩) = s j := div_mul_cancel₀ _ hn0
          linear_combination (n (σ ⟨j, hj⟩)) * e + e2
        · have hMk : M (σ ⟨j, hj⟩) k = 0 := by
            by_cases hk : s k ≠ 0
            · have hne : (σ ⟨k, hk⟩ : κ) ≠ σ ⟨j, hj⟩ := by
                intro heq
                have h3 := σ.injective (Subtype.ext heq)
                exact hjk (congrArg Subtype.val h3).symm
              simp [M, hk, hne]
            · simp [M, hk]
          rw [hMk, mul_zero, diagonal_apply_ne _ hjk]
      · intro i _ hi
        have h3 : M i j = 0 := by simp [M, hj, Ne.symm hi]
        rw [h3]; simp
      · intro h3; exact absurd (Finset.mem_univ _) h3
    · have h3 : ∀ i, M i j = 0 := fun i => by simp [M, hj]
      simp only [h3, zero_mul, Finset.sum_const_zero]
      push Not at hj
      by_cases hjk : j = k
      · rw [← hjk, diagonal_apply_eq, hj]
      · rw [diagonal_apply_ne _ hjk]
  refine ⟨U * M * Vᵀ, ?_⟩
  have hU' : ∀ X : Matrix κ ι ℝ, Uᵀ * (U * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hU1, Matrix.one_mul]
  have hM' : ∀ X : Matrix ι ι ℝ, Mᵀ * (diagonal n * (M * X)) = diagonal s * X := fun X => by
    rw [← hM]; simp only [Matrix.mul_assoc]
  rw [hNU, hSV]
  simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc, hU', hM']

end QMIAux

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    (ZZero P).Nonempty ↔ (schur P).rank ≤ P.toBlocks₂₂.rank := by
  obtain ⟨W, hQ⟩ := QMIAux.qmi_eq P hP
  obtain ⟨hH, hN, hS, hker⟩ := hP
  constructor
  · rintro ⟨Z, hZ⟩
    have hZ' : qmiForm P Z = 0 := hZ
    rw [hQ] at hZ'
    have h1 : schur P = (-(Z + W)ᵀ) * (P.toBlocks₂₂ * (Z + W)) := by
      rw [Matrix.neg_mul, ← Matrix.mul_assoc]
      exact eq_neg_of_add_eq_zero_left hZ'
    rw [h1]
    exact (rank_mul_le_right _ _).trans (rank_mul_le_left _ _)
  · intro h
    have hr : (schur P).rank ≤ (-P.toBlocks₂₂).rank := by
      calc (schur P).rank ≤ P.toBlocks₂₂.rank := h
        _ = ((-P.toBlocks₂₂) * (-1)).rank := by simp
        _ ≤ (-P.toBlocks₂₂).rank := rank_mul_le_left _ _
    obtain ⟨Y, hY⟩ := QMIAux.exists_conj (schur P) (-P.toBlocks₂₂) hS hN hr
    refine ⟨Y - W, ?_⟩
    show qmiForm P (Y - W) = 0
    rw [hQ, sub_add_cancel]
    have h2 : Yᵀ * P.toBlocks₂₂ * Y = -schur P := by
      rw [← hY]; simp
    rw [h2, add_neg_cancel]
