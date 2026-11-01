-- Prove2me | solution 1 for ShapleySnowSG.Kernel.lemma_C1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T21:29:17.806321+00:00
-- url     : https://prove2.me/submissions/2a41a9f8-7f3e-402a-9377-aaf3e63fb2d5

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_MatrixGame

open Matrix Polynomial

namespace SSKAux

lemma C1_core {m : Type*} [Fintype m] [DecidableEq m] (C B : Matrix m m ℝ) (x y : m → ℝ)
    (hx : Cᵀ *ᵥ x = 0) (hy : C *ᵥ y = 0) (hxy : x ⬝ᵥ (B *ᵥ y) ≠ 0) :
    ∃ ε : ℝ, C.rank < (C + ε • B).rank := by
  obtain ⟨V, U, e, hV, hU, hVU⟩ := Matrix.exists_rank_normal_form C
  have hVd : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have hUd : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
  let D0 : Matrix (Fin C.rank ⊕ Fin (Fintype.card m - C.rank)) (Fin C.rank ⊕ Fin (Fintype.card m - C.rank)) ℝ :=
    fromBlocks 1 0 0 0
  let B' : Matrix (Fin C.rank ⊕ Fin (Fintype.card m - C.rank)) (Fin C.rank ⊕ Fin (Fintype.card m - C.rank)) ℝ :=
    (V * B * U).submatrix e.symm e.symm
  have hrank : ∀ ε : ℝ, (C + ε • B).rank = (D0 + ε • B').rank := by
    intro ε
    have h1 : (V * (C + ε • B) * U).rank = (C + ε • B).rank := by
      rw [rank_mul_eq_left_of_isUnit_det U _ hUd, rank_mul_eq_right_of_isUnit_det V _ hVd]
    have h2 : D0 + ε • B' = (V * (C + ε • B) * U).submatrix e.symm e.symm := by
      rw [Matrix.mul_add, Matrix.add_mul, hVU, Matrix.mul_smul, Matrix.smul_mul]
      ext i j
      simp [D0, B']
    rw [h2, rank_submatrix, h1]
  -- kernel vectors in the new coordinates
  set Y : m → ℝ := U⁻¹ *ᵥ y with hY
  set X : m → ℝ := (V⁻¹)ᵀ *ᵥ x with hX
  have hyY : U *ᵥ Y = y := by
    rw [hY, mulVec_mulVec, mul_nonsing_inv U hUd, one_mulVec]
  have hxX : Vᵀ *ᵥ X = x := by
    rw [hX, mulVec_mulVec, ← transpose_mul, nonsing_inv_mul V hVd, transpose_one, one_mulVec]
  have hDY : (V * C * U) *ᵥ Y = 0 := by
    rw [← mulVec_mulVec, hyY, ← mulVec_mulVec, hy, mulVec_zero]
  have hDX : (V * C * U)ᵀ *ᵥ X = 0 := by
    rw [transpose_mul, transpose_mul, ← mulVec_mulVec, ← mulVec_mulVec, hxX, hx, mulVec_zero]
  have hBXY : X ⬝ᵥ ((V * B * U) *ᵥ Y) ≠ 0 := by
    rwa [← mulVec_mulVec, hyY, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hxX]
  set Y' := Y ∘ e.symm with hY'
  set X' := X ∘ e.symm with hX'
  have hY'0 : ∀ a, Y' (Sum.inl a) = 0 := by
    intro a
    have h := congrFun hDY (e.symm (Sum.inl a))
    rw [hVU, submatrix_mulVec_equiv] at h
    show Y (e.symm (Sum.inl a)) = 0
    simpa [D0, fromBlocks_mulVec] using h
  have hX'0 : ∀ a, X' (Sum.inl a) = 0 := by
    intro a
    have h := congrFun hDX (e.symm (Sum.inl a))
    rw [hVU, transpose_submatrix, submatrix_mulVec_equiv] at h
    show X (e.symm (Sum.inl a)) = 0
    simpa [D0, fromBlocks_transpose, fromBlocks_mulVec] using h
  have hB'XY : X' ⬝ᵥ (B' *ᵥ Y') ≠ 0 := by
    have : B' *ᵥ Y' = ((V * B * U) *ᵥ Y) ∘ e.symm := by
      have hc : (Y ∘ e.symm) ∘ e = Y := by ext; simp
      simp only [B', hY', submatrix_mulVec_equiv, Equiv.symm_symm, hc]
    rw [this, hX', comp_equiv_symm_dotProduct]
    have hc : (((V * B * U) *ᵥ Y) ∘ e.symm) ∘ e = (V * B * U) *ᵥ Y := by ext; simp
    rwa [hc]
  obtain ⟨i0, j0, hβ⟩ : ∃ i0 j0, B' (Sum.inr i0) (Sum.inr j0) ≠ 0 := by
    by_contra h
    push Not at h
    apply hB'XY
    simp only [dotProduct, mulVec]
    refine Finset.sum_eq_zero fun t _ => ?_
    rcases t with a | a
    · rw [hX'0 a, zero_mul]
    · rw [Finset.sum_eq_zero, mul_zero]
      intro t' _
      rcases t' with b | b
      · rw [hY'0 b, mul_zero]
      · rw [h a b, zero_mul]
  -- the bordered minor
  let ρ : Fin C.rank ⊕ Unit → Fin C.rank ⊕ Fin (Fintype.card m - C.rank) := Sum.elim Sum.inl (fun _ => Sum.inr i0)
  let κ : Fin C.rank ⊕ Unit → Fin C.rank ⊕ Fin (Fintype.card m - C.rank) := Sum.elim Sum.inl (fun _ => Sum.inr j0)
  let N : ℝ → Matrix (Fin C.rank ⊕ Unit) (Fin C.rank ⊕ Unit) ℝ := fun ε => Matrix.of fun a b =>
    Sum.elim (fun b' => (D0 + ε • B') (ρ a) (Sum.inl b')) (fun _ => B' (ρ a) (Sum.inr j0)) b
  have hfac : ∀ ε : ℝ, (D0 + ε • B').submatrix ρ κ =
      N ε * diagonal (Sum.elim (fun _ => (1 : ℝ)) (fun _ => ε)) := by
    intro ε
    ext a b
    rcases b with b | b
    · simp [N, κ, mul_diagonal]
    · rcases a with a | a <;> simp [N, κ, ρ, mul_diagonal, D0, mul_comm]
  have hcont : Continuous fun ε : ℝ => (N ε).det := by
    refine Continuous.matrix_det ?_
    refine continuous_pi fun a => continuous_pi fun b => ?_
    rcases b with b | b
    · simp only [N, Matrix.of_apply, Sum.elim_inl, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      fun_prop
    · simp only [N, Matrix.of_apply, Sum.elim_inr]
      fun_prop
  have h0 : (N 0).det = B' (Sum.inr i0) (Sum.inr j0) := by
    have : N 0 = fromBlocks 1 (Matrix.of fun a (_ : Unit) => B' (Sum.inl a) (Sum.inr j0)) 0
        (Matrix.of fun (_ _ : Unit) => B' (Sum.inr i0) (Sum.inr j0)) := by
      ext a b
      rcases a with a | a <;> rcases b with b | b <;> simp [N, ρ, D0]
    rw [this, det_fromBlocks_zero₂₁, det_one, one_mul, det_unique]
    rfl
  have hev : ∀ᶠ ε in nhds (0 : ℝ), (N ε).det ≠ 0 :=
    hcont.continuousAt.eventually_ne (by rw [h0]; exact hβ)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ / 2, ?_⟩
  have hNd : (N (δ / 2)).det ≠ 0 := hδ' (by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have hsub : ((D0 + (δ / 2) • B').submatrix ρ κ).det ≠ 0 := by
    rw [hfac, det_mul, det_diagonal, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one, Finset.prod_const,
      Finset.card_univ, Fintype.card_unit, pow_one, one_mul]
    exact mul_ne_zero hNd (by linarith)
  have h1 := rank_of_det_ne_zero hsub
  have h2 := rank_submatrix_le (D0 + (δ / 2) • B') ρ κ
  rw [hrank]
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at h1
  omega

end SSKAux

theorem solution {m : Type*} [Fintype m] [DecidableEq m] (A B : Matrix m m ℝ) (v : ℝ)
    (_hdet : (A + v • B).det = 0) (x y : m → ℝ) (hx : (A + v • B)ᵀ *ᵥ x = 0)
    (hy : (A + v • B) *ᵥ y = 0) (hxy : x ⬝ᵥ (B *ᵥ y) ≠ 0) :
    ∃ w : ℝ, (A + v • B).rank < (A + w • B).rank := by
  obtain ⟨ε, hε⟩ := SSKAux.C1_core (A + v • B) B x y hx hy hxy
  refine ⟨v + ε, ?_⟩
  rwa [add_smul, ← add_assoc]
