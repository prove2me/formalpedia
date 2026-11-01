-- Prove2me | solution 1 for ShapleySnowSG.Kernel.lemma_B3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T21:47:12.385604+00:00
-- url     : https://prove2.me/submissions/46971328-3d09-4aad-9207-1eb70d113b00

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_MatrixGame

open Matrix

namespace SSKAux

lemma exists_minor_ne_zero {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix ι κ ℝ) : ∃ (f : Fin M.rank ↪ ι) (h : Fin M.rank ↪ κ), (M.submatrix f h).det ≠ 0 := by
  obtain ⟨κ1, a, ha_inj, hspan, hli⟩ := exists_linearIndependent' ℝ M.row
  have : Finite κ1 := Finite.of_injective a ha_inj
  have : Fintype κ1 := Fintype.ofFinite κ1
  have hcard : Fintype.card κ1 = M.rank := by
    rw [linearIndependent_iff_card_eq_finrank_span.mp hli, M.rank_eq_finrank_span_row]
    show Module.finrank ℝ (Submodule.span ℝ (Set.range (M.row ∘ a))) = _
    rw [hspan]
  let ea : Fin M.rank ≃ κ1 := (Fintype.equivFinOfCardEq hcard).symm
  let f : Fin M.rank ↪ ι := ⟨a ∘ ea, ha_inj.comp ea.injective⟩
  let M1 : Matrix (Fin M.rank) κ ℝ := M.submatrix f id
  have hli1 : LinearIndependent ℝ M1.row := by
    have : M1.row = (M.row ∘ a) ∘ ea := rfl
    rw [this]
    exact hli.comp ea ea.injective
  have hr1 : M1.rank = M.rank := by
    rw [hli1.rank_matrix, Fintype.card_fin]
  obtain ⟨κ2, b, hb_inj, hspan2, hli2⟩ := exists_linearIndependent' ℝ M1.col
  have : Finite κ2 := Finite.of_injective b hb_inj
  have : Fintype κ2 := Fintype.ofFinite κ2
  have hcard2 : Fintype.card κ2 = M.rank := by
    rw [linearIndependent_iff_card_eq_finrank_span.mp hli2]
    show Module.finrank ℝ (Submodule.span ℝ (Set.range (M1.col ∘ b))) = _
    rw [hspan2, ← M1.rank_eq_finrank_span_cols, hr1]
  let eb : Fin M.rank ≃ κ2 := (Fintype.equivFinOfCardEq hcard2).symm
  let h : Fin M.rank ↪ κ := ⟨b ∘ eb, hb_inj.comp eb.injective⟩
  refine ⟨f, h, ?_⟩
  have hli3 : LinearIndependent ℝ (M.submatrix f h).col := by
    have : (M.submatrix f h).col = (M1.col ∘ b) ∘ eb := rfl
    rw [this]
    exact hli2.comp eb eb.injective
  have hU := Matrix.linearIndependent_cols_iff_isUnit.mp hli3
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hU).ne_zero

lemma succAbove_reindex {n : ℕ} (i0 : Fin (n + 1)) (f : Fin n → Fin (n + 1))
    (hfi : Function.Injective f) (hf : ∀ k, f k ≠ i0) :
    ∃ σ : Equiv.Perm (Fin n), ∀ k, i0.succAbove (σ k) = f k := by
  choose σ0 hσ0 using fun k => Fin.exists_succAbove_eq (hf k)
  have inj : Function.Injective σ0 := fun a b hab => hfi (by rw [← hσ0 a, ← hσ0 b, hab])
  exact ⟨Equiv.ofBijective σ0 (Finite.injective_iff_bijective.mp inj), fun k => hσ0 k⟩

end SSKAux

open ShapleySnowSG.Kernel in
theorem solution {a : ℕ} (ha : 0 < a) (M : Matrix (Fin a) (Fin a) ℝ) (hrank : M.rank = a - 1)
    (x y : Fin a → ℝ) (hx : LinearMap.ker Mᵀ.mulVecLin = ℝ ∙ x)
    (hy : LinearMap.ker M.mulVecLin = ℝ ∙ y) :
    ∃ α : ℝ, α ≠ 0 ∧ co M = α • vecMulVec x y := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  have hr : M.rank = n := by rw [hrank]; simp
  obtain ⟨f, h, hfh⟩ := SSKAux.exists_minor_ne_zero M
  have key : ∀ (r : ℕ) (hr : r = n) (f h : Fin r ↪ Fin (n + 1)),
      (M.submatrix f h).det ≠ 0 → ∃ i0 j0 : Fin (n + 1),
        (M.submatrix i0.succAbove j0.succAbove).det ≠ 0 := by
    intro r hr f h hfh
    subst hr
    have hex : ∀ g : Fin r ↪ Fin (r + 1), ∃ i0, ∀ k, g k ≠ i0 := by
      intro g
      by_contra hc
      push Not at hc
      have hs : Function.Surjective g := fun i => (hc i)
      have := Fintype.card_le_of_surjective g hs
      simp only [Fintype.card_fin] at this
      omega
    obtain ⟨i0, hi0⟩ := hex f
    obtain ⟨j0, hj0⟩ := hex h
    obtain ⟨σ, hσ⟩ := SSKAux.succAbove_reindex i0 f f.injective hi0
    obtain ⟨τ, hτ⟩ := SSKAux.succAbove_reindex j0 h h.injective hj0
    refine ⟨i0, j0, fun h0 => hfh ?_⟩
    have : M.submatrix f h =
        ((M.submatrix i0.succAbove j0.succAbove).submatrix σ id).submatrix id τ := by
      ext k l; simp [hσ, hτ]
    rw [this, det_permute', det_permute, h0, mul_zero, mul_zero]
  obtain ⟨i0, j0, hij⟩ := key M.rank hr f h hfh
  have hadj : M.adjugate j0 i0 ≠ 0 := by
    rw [adjugate_fin_succ_eq_det_submatrix]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hij
  have hdetM : M.det = 0 := by
    by_contra hd
    have := rank_of_det_ne_zero hd
    rw [Fintype.card_fin] at this
    omega
  have hMA : M * M.adjugate = 0 := by rw [mul_adjugate, hdetM, zero_smul]
  have hAM : M.adjugate * M = 0 := by rw [adjugate_mul, hdetM, zero_smul]
  have hcol : ∀ i, ∃ ci : ℝ, ∀ j, M.adjugate j i = ci * y j := by
    intro i
    have hv : (fun j => M.adjugate j i) ∈ LinearMap.ker M.mulVecLin := by
      rw [LinearMap.mem_ker, mulVecLin_apply]
      ext l
      have := congrFun (congrFun hMA l) i
      simpa [mulVec, dotProduct, Matrix.mul_apply] using this
    rw [hy, Submodule.mem_span_singleton] at hv
    obtain ⟨ci, hci⟩ := hv
    exact ⟨ci, fun j => by have := congrFun hci j; simp at this; linarith⟩
  have hrow : ∀ j, ∃ dj : ℝ, ∀ i, M.adjugate j i = dj * x i := by
    intro j
    have hv : (fun i => M.adjugate j i) ∈ LinearMap.ker Mᵀ.mulVecLin := by
      rw [LinearMap.mem_ker, mulVecLin_apply]
      ext l
      have := congrFun (congrFun hAM j) l
      simpa [mulVec, dotProduct, Matrix.mul_apply, mul_comm] using this
    rw [hx, Submodule.mem_span_singleton] at hv
    obtain ⟨dj, hdj⟩ := hv
    exact ⟨dj, fun i => by have := congrFun hdj i; simp at this; linarith⟩
  choose cc hc using hcol
  choose dd hd using hrow
  have hx0 : x i0 ≠ 0 := by
    intro h0; apply hadj; rw [hd, h0, mul_zero]
  have hc0 : cc i0 ≠ 0 := by
    intro h0; apply hadj; rw [hc, h0, zero_mul]
  refine ⟨cc i0 / x i0, div_ne_zero hc0 hx0, ?_⟩
  ext i j
  have h1 := hd j i
  have h2 := hd j i0
  rw [hc] at h2
  simp only [co, transpose_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  rw [h1]
  have : dd j = cc i0 * y j / x i0 := by field_simp; linarith
  rw [this]
  field_simp
