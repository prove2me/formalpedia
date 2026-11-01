-- Prove2me | solution 1 for ShapleySnowSG.Kernel.prop_3_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T21:39:46.408431+00:00
-- url     : https://prove2.me/submissions/e31e822f-1be6-4b74-898f-b2253006159d

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_StochasticGame

open Matrix Polynomial

namespace SSKAux
open ShapleySnowSG.Kernel

lemma det_rows_sum {K : Type*} [Field K] {n : ℕ} {q : Fin n → Type*} [∀ k, Fintype (q k)]
    (F : ∀ k : Fin n, q k → Fin n → K) (y : ∀ k, q k → K) :
    ∑ j : (∀ k, q k), (Matrix.of fun k m => F k (j k) m).det * ∏ k, y k (j k)
      = (Matrix.of fun k m => ∑ b, F k b m * y k b).det := by
  have h1 : (Matrix.of fun k m => ∑ b, F k b m * y k b) = fun k => ∑ b, y k b • F k b := by
    ext k m; simp [Finset.sum_apply, mul_comm]
  rw [h1]
  have := (Matrix.detRowAlternating (n := Fin n) (R := K)).toMultilinearMap.map_sum
    (fun k b => y k b • F k b)
  change _ = (Matrix.detRowAlternating (n := Fin n) (R := K)).toMultilinearMap _
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]
  rfl

lemma aux_mulVec_tensor {K : Type*} [Field K] {n : ℕ} {p q : Fin n → Type*}
    [∀ k, Fintype (q k)]
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (q k) K) (y : ∀ k, q k → K)
    (ℓ : Fin (n + 1)) (i : ∀ k, p k) :
    (aux M ℓ *ᵥ tensorVec y) i =
      (-1) ^ (ℓ : ℕ) * (Matrix.of fun k m => (M k (ℓ.succAbove m) *ᵥ y k) (i k)).det := by
  simp only [mulVec, dotProduct, aux, kronDet, tensorVec, Matrix.smul_apply, smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  exact det_rows_sum (fun k b m => M k (ℓ.succAbove m) (i k) b) y

lemma kron_kernel {K : Type*} [Field K] {n : ℕ} {p q : Fin n → Type*}
    [∀ k, Fintype (q k)]
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (q k) K) (z : Fin n → K) (y : ∀ k, q k → K)
    (hy : ∀ k, pencil M z k *ᵥ y k = 0) (k : Fin n) :
    (aux M k.succ - z k • aux M 0) *ᵥ tensorVec y = 0 := by
  funext i
  set a : Matrix (Fin n) (Fin (n + 1)) K := Matrix.of fun k' l => (M k' l *ᵥ y k') (i k') with ha_def
  let u : Fin (n + 1) → K := Fin.cons 1 z
  have ha : ∀ k', ∑ l, a k' l * u l = 0 := by
    intro k'
    have := congrFun (hy k') (i k')
    rw [Fin.sum_univ_succ]
    simp only [pencil, add_mulVec, Matrix.sum_mulVec, smul_mulVec, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [ha_def, u, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, mul_one]
    rw [← this]
    congr 1
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  let e : Fin (n + 1) → K := fun j => (if j = k.succ then 1 else 0) - z k * (if j = 0 then 1 else 0)
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of (Fin.cons e (fun k' => a k'))
  have hB : B.det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨u, ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp [u] at this
    · funext j
      refine Fin.cases ?_ (fun k' => ?_) j
      · simp only [mulVec, dotProduct, B, Matrix.of_apply, Fin.cons_zero, e, Pi.zero_apply]
        rw [Fin.sum_univ_succ]
        simp [u, Fin.succ_ne_zero, Finset.sum_ite_eq', Fin.succ_inj, (Fin.succ_ne_zero k).symm]
      · simp only [mulVec, dotProduct, B, Matrix.of_apply, Fin.cons_succ, Pi.zero_apply]
        exact ha k'
  rw [det_succ_row_zero] at hB
  simp only [B, Matrix.of_apply, Fin.cons_zero, e, Matrix.submatrix, Fin.cons_succ] at hB
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hB
  rw [sub_mulVec, Pi.sub_apply, smul_mulVec, Pi.smul_apply, smul_eq_mul,
    aux_mulVec_tensor, aux_mulVec_tensor, Pi.zero_apply]
  rw [← hB]
  simp only [Fin.val_zero, pow_zero, one_mul, a]
  rfl

lemma tensorVec_ne_zero {K : Type*} [Field K] {n : ℕ} {q : Fin n → Type*}
    (y : ∀ k, q k → K) (hy0 : ∀ k, y k ≠ 0) : tensorVec y ≠ 0 := by
  have : ∀ k, ∃ b, y k b ≠ 0 := fun k => by
    by_contra h
    push Not at h
    exact hy0 k (funext h)
  choose b hb using this
  intro h
  have := congrFun h b
  simp only [tensorVec, Pi.zero_apply] at this
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => hb k) this

end SSKAux



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



open Matrix Polynomial

namespace SSKAux
open ShapleySnowSG.Kernel

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

lemma natDegree_det_block_le {r s : ℕ} (A : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ) :
    (A.map C - (X : ℝ[X]) • (fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0).map C).det.natDegree
      ≤ r := by
  set Mx : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ[X] :=
    A.map C - (X : ℝ[X]) • (fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0).map C with hMx
  rw [det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  have hb : ∀ i, (Mx (σ i) i).natDegree ≤ Sum.elim (fun _ => 1) (fun _ => 0) i := by
    intro i
    simp only [hMx, Matrix.sub_apply, Matrix.smul_apply, map_apply, smul_eq_mul]
    rcases i with i | i
    · simp only [Sum.elim_inl]
      refine (natDegree_sub_le _ _).trans ?_
      simp only [natDegree_C, zero_le, max_le_iff, true_and]
      exact natDegree_mul_le.trans (by simp)
    · have : fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 (σ (Sum.inr i)) (Sum.inr i) = 0 := by
        rcases σ (Sum.inr i) with j | j <;> simp
      simp [this]
  refine (Finset.sum_le_sum fun i _ => hb i).trans ?_
  simp [Fintype.sum_sum_type]

lemma natDegree_det_pencil_le {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ) :
    (A.map C - (X : ℝ[X]) • B.map C).det.natDegree ≤ B.rank := by
  obtain ⟨V, U, e, hV, hU, hVU⟩ := Matrix.exists_rank_normal_form B
  have hVd : V.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det V).mp hV).ne_zero
  have hUd : U.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det U).mp hU).ne_zero
  have key : (V.map C) * (A.map C - (X : ℝ[X]) • B.map C) * (U.map C) =
      (V * A * U).map C - (X : ℝ[X]) • (V * B * U).map C := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have key2 : (V * A * U).map C - (X : ℝ[X]) • (V * B * U).map C =
      ((((V * A * U).submatrix e.symm e.symm).map C - (X : ℝ[X]) •
        (fromBlocks (1 : Matrix (Fin B.rank) (Fin B.rank) ℝ) 0 0 0).map C)).submatrix e e := by
    rw [hVU]; generalize V * A * U = W; ext i j; simp
  have hVC : (V.map C).det = C V.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hUC : (U.map C).det = C U.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hdet := congrArg Matrix.det (key.trans key2)
  rw [det_mul, det_mul, det_submatrix_equiv_self, hVC, hUC] at hdet
  have := natDegree_det_block_le (r := B.rank) ((V * A * U).submatrix e.symm e.symm)
  rw [← hdet, mul_comm (C V.det), mul_assoc, ← C_mul] at this
  rwa [natDegree_mul_C (mul_ne_zero hVd hUd)] at this

lemma eval_det_pencil {ι κ : Type*} [Fintype κ] [DecidableEq κ] (A B : Matrix ι ι ℝ)
    (f h : κ → ι) (t : ℝ) :
    (((A.map C - (X : ℝ[X]) • B.map C).submatrix f h).det).eval t =
      ((A - t • B).submatrix f h).det := by
  rw [← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, map_apply, submatrix_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, coe_evalRingHom, eval_sub, eval_C, eval_mul, eval_X]

lemma rankdrop_poly {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (z : ℝ)
    (hz : RankDrop A B z) :
    ∃ (m : ℕ) (f h : Fin m ↪ ι),
      (((A.map C - (X : ℝ[X]) • B.map C).submatrix f h).det).eval z = 0 ∧
      ((A.map C - (X : ℝ[X]) • B.map C).submatrix f h).det ≠ 0 ∧
      ((A.map C - (X : ℝ[X]) • B.map C).submatrix f h).det.natDegree ≤ B.rank := by
  obtain ⟨w, hw⟩ := hz
  obtain ⟨f, h, hdet⟩ := exists_minor_ne_zero (A - w • B)
  refine ⟨_, f, h, ?_, ?_, ?_⟩
  · rw [eval_det_pencil]
    by_contra hne
    have h1 := rank_of_det_ne_zero hne
    have h2 := rank_submatrix_le (A - z • B) f h
    rw [Fintype.card_fin] at h1
    omega
  · intro h0
    have := eval_det_pencil A B f h w
    rw [h0, eval_zero] at this
    exact hdet this.symm
  · have : (A.map C - (X : ℝ[X]) • B.map C).submatrix f h =
        (A.submatrix f h).map C - (X : ℝ[X]) • (B.submatrix f h).map C := by
      ext i j; simp
    rw [this]
    exact (natDegree_det_pencil_le _ _).trans (rank_submatrix_le B f h)

end SSKAux


open Matrix Polynomial

namespace SSKAux
open ShapleySnowSG.Kernel

lemma val_le {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (x : ι → ℝ) (y : κ → ℝ)
    (w w' : ℝ) (hx : x ∈ stdSimplex ℝ ι) (hy : y ∈ stdSimplex ℝ κ)
    (h1 : ∀ j, w ≤ ∑ i, x i * A i j) (h2 : ∀ i, ∑ j, A i j * y j ≤ w') : w ≤ w' := by
  calc w = ∑ j, y j * w := by rw [← Finset.sum_mul, hy.2, one_mul]
    _ ≤ ∑ j, y j * ∑ i, x i * A i j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h1 j) (hy.1 j)
    _ = ∑ i, x i * ∑ j, A i j * y j := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ i, x i * w' := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h2 i) (hx.1 i)
    _ = w' := by rw [← Finset.sum_mul, hx.2, one_mul]

lemma isMatVal_unique {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (w w' : ℝ)
    (h : IsMatVal A w) (h' : IsMatVal A w') : w = w' := by
  obtain ⟨x, hx, y, hy, hxA, hAy⟩ := h
  obtain ⟨x', hx', y', hy', hxA', hAy'⟩ := h'
  exact le_antisymm (val_le A x y' w w' hx hy' hxA hAy') (val_le A x' y w' w hx' hy hxA' hAy)

lemma sum_extend_mul {ι : Type*} [Fintype ι] {s : ℕ} (r : Fin s ↪ ι) (f : Fin s → ℝ)
    (φ : ι → ℝ) : ∑ i, Function.extend r f 0 i * φ i = ∑ a, f a * φ (r a) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map r))]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Function.Embedding.coeFn_mk] at *
    simp [r.injective.extend_apply]
  · intro i _ hi
    have : ∀ a, r a ≠ i := fun a ha => hi (by simp [← ha])
    rw [Function.extend_apply' _ _ _ (by rintro ⟨a, ha⟩; exact this a ha)]
    simp

lemma ssk_facts {ι κ : Type*} [Fintype ι] [Fintype κ] (G : Matrix ι κ ℝ) (w : ℝ)
    (hw : IsMatVal G w) (s : ℕ) (r : Fin s ↪ ι) (c : Fin s ↪ κ) (hK : IsSSK G s r c) :
    ssRow G s r c ∈ stdSimplex ℝ (Fin s) ∧ ssCol G s r c ∈ stdSimplex ℝ (Fin s) ∧
    (subGame G s r c - w • onesMat (Fin s) (Fin s)) *ᵥ ssCol G s r c = 0 ∧
    ssRow G s r c ᵥ* (subGame G s r c - w • onesMat (Fin s) (Fin s)) = 0 := by
  obtain ⟨hS, ⟨hxs, w1, hw1, hx1⟩, ⟨hys, w2, hw2, hy2⟩⟩ := hK
  have e1 : w1 = w := isMatVal_unique G w1 w hw1 hw
  have e2 : w2 = w := isMatVal_unique G w2 w hw2 hw
  rw [e1] at hx1
  rw [e2] at hy2
  set Gd := subGame G s r c with hGd
  set S := Ssum (co Gd) with hSdef
  have hrow : ∀ a, padRow G s r c (r a) = ssRow G s r c a := fun a =>
    r.injective.extend_apply _ _ a
  have hcol : ∀ b, padCol G s r c (c b) = ssCol G s r c b := fun b =>
    c.injective.extend_apply _ _ b
  have hrowsum : ∑ a, ssRow G s r c a = 1 := by
    simp only [ssRow, ← Finset.sum_div, mulVec, dotProduct, mul_one]
    rw [← hGd, ← hSdef]
    exact div_self hS
  have hcolsum : ∑ b, ssCol G s r c b = 1 := by
    simp only [ssCol, ← Finset.sum_div, mulVec, dotProduct, mul_one, transpose_apply]
    rw [← hGd, ← hSdef, Finset.sum_comm]
    exact div_self hS
  have hxS : ssRow G s r c ∈ stdSimplex ℝ (Fin s) :=
    ⟨fun a => by rw [← hrow]; exact hxs.1 _, hrowsum⟩
  have hyS : ssCol G s r c ∈ stdSimplex ℝ (Fin s) :=
    ⟨fun b => by rw [← hcol]; exact hys.1 _, hcolsum⟩
  have hyeq : ssCol G s r c = S⁻¹ • (Gd.adjugate *ᵥ fun _ => (1 : ℝ)) := by
    ext b
    simp [ssCol, co, div_eq_inv_mul, hGd, hSdef]
  have hxeq : ssRow G s r c = S⁻¹ • ((fun _ => (1 : ℝ)) ᵥ* Gd.adjugate) := by
    ext a
    simp only [ssRow, div_eq_inv_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    rw [co, mulVec_transpose]
  have hGy : Gd *ᵥ ssCol G s r c = fun _ => S⁻¹ * Gd.det := by
    rw [hyeq, mulVec_smul, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]
    ext a; simp [mul_comm]
  have hxG : ssRow G s r c ᵥ* Gd = fun _ => S⁻¹ * Gd.det := by
    rw [hxeq, smul_vecMul, vecMul_vecMul, adjugate_mul, vecMul_smul, vecMul_one]
    ext a; simp [mul_comm]
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · exfalso; apply hS; rw [hSdef, Ssum]; subst h; simp
    · exact h
  have hc1 : w ≤ S⁻¹ * Gd.det := by
    have := hx1 (c ⟨0, hs⟩)
    simp only [padRow] at this
    rw [sum_extend_mul r] at this
    have h2 : ∑ x, ssRow G s r c x * G (r x) (c ⟨0, hs⟩) = S⁻¹ * Gd.det :=
      congrFun hxG ⟨0, hs⟩
    linarith
  have hc2 : S⁻¹ * Gd.det ≤ w := by
    have := hy2 (r ⟨0, hs⟩)
    simp_rw [mul_comm (G _ _)] at this
    simp only [padCol] at this
    rw [sum_extend_mul c] at this
    have h2 : ∑ x, G (r ⟨0, hs⟩) (c x) * ssCol G s r c x = S⁻¹ * Gd.det :=
      congrFun hGy ⟨0, hs⟩
    have h3 : ∑ a, ssCol G s r c a * G (r ⟨0, hs⟩) (c a) =
        ∑ a, G (r ⟨0, hs⟩) (c a) * ssCol G s r c a :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    linarith
  have hval : S⁻¹ * Gd.det = w := le_antisymm hc2 hc1
  refine ⟨hxS, hyS, ?_, ?_⟩
  · rw [sub_mulVec, hGy, smul_mulVec]
    ext a
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mulVec, dotProduct,
      onesMat, Matrix.of_apply, one_mul, hcolsum, hval]
    ring
  · rw [vecMul_sub, hxG, vecMul_smul]
    ext b
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, vecMul, dotProduct,
      onesMat, Matrix.of_apply, mul_one, hrowsum, hval]
    ring

lemma pencil_red {n : ℕ} {I J : Fin n → Type*} (g : ∀ k, I k → J k → ℝ)
    (q : ∀ k, I k → J k → Fin n → ℝ) (lam : ℝ) (v : Fin n → ℝ) (s : Fin n → ℕ)
    (r : ∀ k, Fin (s k) ↪ I k) (c : ∀ k, Fin (s k) ↪ J k) (k : Fin n) :
    pencil (redArray (dataArray g q lam) s r c) v k =
      subGame (localGame g q lam v k) (s k) (r k) (c k) - v k • onesMat _ _ := by
  ext a b
  simp only [pencil, redArray, dataArray, subGame, localGame, onesMat, Matrix.add_apply,
    Matrix.sum_apply, Matrix.smul_apply, submatrix_apply, Matrix.of_apply, Fin.cases_zero,
    Fin.cases_succ, smul_eq_mul, Matrix.sub_apply, mul_one]
  simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.mul_sum]
  rw [← add_sub_assoc]
  congr 2
  exact Finset.sum_congr rfl fun l _ => by ring

lemma tensor_stdSimplex {n : ℕ} {p : Fin n → Type*} [∀ k, Fintype (p k)]
    (x : ∀ k, p k → ℝ) (hx : ∀ k, x k ∈ stdSimplex ℝ (p k)) :
    tensorVec x ∈ stdSimplex ℝ (∀ k, p k) := by
  refine ⟨fun i => Finset.prod_nonneg fun k _ => (hx k).1 _, ?_⟩
  simp only [tensorVec]
  rw [← Fintype.prod_sum]
  simp [(hx _).2]

lemma aux_transpose {n : ℕ} {p q : Fin n → Type*}
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (q k) ℝ) (ℓ : Fin (n + 1)) :
    aux (fun k l => (M k l)ᵀ) ℓ = (aux M ℓ)ᵀ := by
  ext i j
  rfl

lemma pencil_transpose {n : ℕ} {p q : Fin n → Type*}
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (q k) ℝ) (z : Fin n → ℝ) (k : Fin n) :
    pencil (fun k l => (M k l)ᵀ) z k = (pencil M z k)ᵀ := by
  simp [pencil, transpose_add, transpose_sum, transpose_smul]

lemma det_one_sub_pos {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ0 : ∀ i j, 0 ≤ Q i j)
    (hQ1 : ∀ i, ∑ j, Q i j = 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) : 0 < (1 - t • Q).det := by
  have hne : ∀ u ∈ Set.Icc 0 t, (1 - u • Q).det ≠ 0 := by
    intro u ⟨hu0, hut⟩
    apply det_ne_zero_of_sum_row_lt_diag
    intro k
    have hoff : ∀ j ∈ Finset.univ.erase k, ‖(1 - u • Q) k j‖ = u * Q k j := by
      intro j hj
      rw [Matrix.sub_apply, one_apply_ne (Finset.ne_of_mem_erase hj).symm, Matrix.smul_apply,
        smul_eq_mul, zero_sub, norm_neg, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hu0 (hQ0 k j))]
    have hkk : Q k k ≤ 1 := by
      rw [← hQ1 k]
      exact Finset.single_le_sum (fun j _ => hQ0 k j) (Finset.mem_univ k)
    rw [Finset.sum_congr rfl hoff, ← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ k),
      hQ1, Matrix.sub_apply, one_apply_eq, Matrix.smul_apply, smul_eq_mul, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith)]
    nlinarith
  have hcont : Continuous fun u : ℝ => (1 - u • Q).det :=
    (continuous_const.sub (continuous_id.smul continuous_const)).matrix_det
  by_contra hle
  push Not at hle
  have h0 : (1 - (0 : ℝ) • Q).det = 1 := by simp
  have := intermediate_value_Icc' ht0 hcont.continuousOn
  obtain ⟨u, hu, hu0⟩ := this ⟨hle, by rw [h0]; norm_num⟩
  exact hne u hu hu0

lemma deltaDot0_sign {n : ℕ} {I J : Fin n → Type*} (g : ∀ k, I k → J k → ℝ)
    (q : ∀ k, I k → J k → Fin n → ℝ) (hq0 : ∀ k i j l, 0 ≤ q k i j l)
    (hq1 : ∀ k i j, ∑ l, q k i j l = 1) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (s : Fin n → ℕ) (r : ∀ k, Fin (s k) ↪ I k) (c : ∀ k, Fin (s k) ↪ J k) (a b : ∀ k, Fin (s k)) :
    0 < (-1) ^ n * DeltaDot g q lam s r c 0 a b := by
  let Q : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun k m => q k (r k (a k)) (c k (b k)) m
  have h : DeltaDot g q lam s r c 0 a b = (-(1 - (1 - lam) • Q)).det := by
    simp only [DeltaDot, aux, kronDet, redArray, dataArray, Fin.val_zero, pow_zero, one_smul]
    congr 1
    ext k m
    simp only [Matrix.of_apply, submatrix_apply, Fin.succAbove_zero, Fin.cases_succ, Q,
      Matrix.neg_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, one_apply]
    by_cases hkm : k = m
    · subst hkm; simp
    · simp [hkm, Ne.symm hkm]
  rw [h, det_neg, Fintype.card_fin, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
    one_pow, one_mul]
  exact det_one_sub_pos Q (fun i j => hq0 _ _ _ _) (fun i => hq1 _ _ _) _ (by linarith)
    (by linarith)

end SSKAux

namespace SSKAux
open ShapleySnowSG.Kernel

lemma dot_pos {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (σ : ℝ) (hB : ∀ a b, 0 < σ * B a b)
    (x y : ι → ℝ) (hx : x ∈ stdSimplex ℝ ι) (hy : y ∈ stdSimplex ℝ ι) :
    0 < σ * (x ⬝ᵥ (B *ᵥ y)) := by
  have hx1 : ∃ a, 0 < x a := by
    by_contra h
    push Not at h
    have : ∑ a, x a = 0 := Finset.sum_eq_zero fun a _ => le_antisymm (h a) (hx.1 a)
    rw [hx.2] at this; exact one_ne_zero this
  have hy1 : ∃ b, 0 < y b := by
    by_contra h
    push Not at h
    have : ∑ a, y a = 0 := Finset.sum_eq_zero fun a _ => le_antisymm (h a) (hy.1 a)
    rw [hy.2] at this; exact one_ne_zero this
  obtain ⟨a0, ha0⟩ := hx1
  obtain ⟨b0, hb0⟩ := hy1
  have : σ * (x ⬝ᵥ (B *ᵥ y)) = ∑ a, ∑ b, x a * y b * (σ * B a b) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [this]
  refine Finset.sum_pos' (fun a _ => Finset.sum_nonneg fun b _ =>
    mul_nonneg (mul_nonneg (hx.1 a) (hy.1 b)) (hB a b).le) ⟨a0, Finset.mem_univ _, ?_⟩
  exact Finset.sum_pos' (fun b _ => mul_nonneg (mul_nonneg (hx.1 a0) (hy.1 b)) (hB a0 b).le)
    ⟨b0, Finset.mem_univ _, mul_pos (mul_pos ha0 hb0) (hB a0 b0)⟩

lemma uniq_root {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) (σ v w : ℝ) (X Y : ι → ℝ)
    (hX : X ∈ stdSimplex ℝ ι) (hY : Y ∈ stdSimplex ℝ ι)
    (hXk : X ᵥ* (A - v • B) = 0) (hYk : (A - v • B) *ᵥ Y = 0)
    (hpos : ∀ x y : ι → ℝ, x ∈ stdSimplex ℝ ι → y ∈ stdSimplex ℝ ι → 0 < σ * (x ⬝ᵥ (B *ᵥ y)))
    (hw : IsMatVal (A - w • B) 0) : w = v := by
  obtain ⟨x', hx', y', hy', h1, h2⟩ := hw
  have hM : A - w • B = (A - v • B) + (v - w) • B := by rw [sub_smul]; abel
  have ha : 0 ≤ (v - w) * (x' ⬝ᵥ (B *ᵥ Y)) := by
    have h0 : 0 ≤ (x' ᵥ* (A - w • B)) ⬝ᵥ Y :=
      Finset.sum_nonneg fun j _ => mul_nonneg (h1 j) (hY.1 j)
    rw [← dotProduct_mulVec, hM, add_mulVec, hYk, zero_add, smul_mulVec, dotProduct_smul,
      smul_eq_mul] at h0
    exact h0
  have hb : (v - w) * (X ⬝ᵥ (B *ᵥ y')) ≤ 0 := by
    have h0 : X ⬝ᵥ ((A - w • B) *ᵥ y') ≤ 0 :=
      Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hX.1 i) (h2 i)
    rw [dotProduct_mulVec, hM, vecMul_add, hXk, zero_add, vecMul_smul, smul_dotProduct,
      smul_eq_mul, ← dotProduct_mulVec] at h0
    exact h0
  have hσa := hpos x' Y hx' hY
  have hσb := hpos X y' hX hy'
  set a := x' ⬝ᵥ (B *ᵥ Y)
  set b := X ⬝ᵥ (B *ᵥ y')
  have hab : 0 < a * b := by
    have h3 : 0 < (σ * a) * (σ * b) := mul_pos hσa hσb
    have h4 : (σ * a) * (σ * b) = σ ^ 2 * (a * b) := by ring
    rw [h4] at h3
    exact pos_of_mul_pos_right h3 (sq_nonneg σ)
  have h5 : (v - w) ^ 2 * (a * b) ≤ 0 := by
    have : (v - w) ^ 2 * (a * b) = ((v - w) * a) * ((v - w) * b) := by ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos ha hb
  have h6 : (v - w) ^ 2 ≤ 0 := by
    by_contra h
    push Not at h
    linarith [mul_pos h hab]
  have : v - w = 0 := by nlinarith [sq_nonneg (v - w)]
  linarith

end SSKAux

open ShapleySnowSG.Kernel in
theorem solution {n : ℕ} (hn : 0 < n) {I J : Fin n → Type*} [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]
    [∀ k, Nonempty (I k)] [∀ k, Nonempty (J k)]
    (g : ∀ k, I k → J k → ℝ) (q : ∀ k, I k → J k → Fin n → ℝ)
    (hq0 : ∀ k i j l, 0 ≤ q k i j l) (hq1 : ∀ k i j, ∑ l, q k i j l = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (v : Fin n → ℝ) (hv : IsShapleyFixed g q lam v)
    (s : Fin n → ℕ) (r : ∀ k, Fin (s k) ↪ I k) (c : ∀ k, Fin (s k) ↪ J k)
    (hK : ∀ k, IsSSK (localGame g q lam v k) (s k) (r k) (c k)) (k : Fin n) :
    ∃ (m : ℕ) (f h : Fin m ↪ (∀ k, Fin (s k))),
      let P : Polynomial ℝ :=
        ((DeltaDot g q lam s r c k.succ).map Polynomial.C -
          (Polynomial.X : Polynomial ℝ) • (DeltaDot g q lam s r c 0).map Polynomial.C).submatrix f h |>.det
      P.eval (v k) = 0 ∧ P ≠ 0 ∧
        P.natDegree ≤ (DeltaDot g q lam s r c 0).rank := by
  have hfacts := fun k => SSKAux.ssk_facts (localGame g q lam v k) (v k) (hv k) (s k) (r k) (c k) (hK k)
  let xd : ∀ k, Fin (s k) → ℝ := fun k => ssRow (localGame g q lam v k) (s k) (r k) (c k)
  let yd : ∀ k, Fin (s k) → ℝ := fun k => ssCol (localGame g q lam v k) (s k) (r k) (c k)
  have hYk : (DeltaDot g q lam s r c k.succ - v k • DeltaDot g q lam s r c 0) *ᵥ tensorVec yd = 0 :=
    SSKAux.kron_kernel (redArray (dataArray g q lam) s r c) v yd
      (fun k' => by rw [SSKAux.pencil_red]; exact (hfacts k').2.2.1) k
  have hXk : tensorVec xd ᵥ* (DeltaDot g q lam s r c k.succ - v k • DeltaDot g q lam s r c 0) = 0 := by
    have := SSKAux.kron_kernel (fun k l => (redArray (dataArray g q lam) s r c k l)ᵀ) v xd
      (fun k' => by
        rw [SSKAux.pencil_transpose, SSKAux.pencil_red, mulVec_transpose]
        exact (hfacts k').2.2.2) k
    rw [SSKAux.aux_transpose, SSKAux.aux_transpose, ← transpose_smul, ← transpose_sub,
      mulVec_transpose] at this
    exact this
  have hXs := SSKAux.tensor_stdSimplex xd (fun k => (hfacts k).1)
  have hYs := SSKAux.tensor_stdSimplex yd (fun k => (hfacts k).2.1)
  have hsign : ∀ a b, 0 < (-1) ^ n * DeltaDot g q lam s r c 0 a b :=
    SSKAux.deltaDot0_sign g q hq0 hq1 lam hlam0 hlam1 s r c
  have hpos := SSKAux.dot_pos (DeltaDot g q lam s r c 0) _ hsign
  have hRD : RankDrop (DeltaDot g q lam s r c k.succ) (DeltaDot g q lam s r c 0) (v k) := by
    have hxy : tensorVec xd ⬝ᵥ (DeltaDot g q lam s r c 0 *ᵥ tensorVec yd) ≠ 0 := by
      have := hpos _ _ hXs hYs
      intro h0; rw [h0, mul_zero] at this; exact lt_irrefl _ this
    obtain ⟨ε, hε⟩ := SSKAux.C1_core
      (DeltaDot g q lam s r c k.succ - v k • DeltaDot g q lam s r c 0)
      (DeltaDot g q lam s r c 0) (tensorVec xd) (tensorVec yd)
      (by rw [mulVec_transpose]; exact hXk) hYk hxy
    refine ⟨v k - ε, ?_⟩
    have : DeltaDot g q lam s r c k.succ - (v k - ε) • DeltaDot g q lam s r c 0 =
        DeltaDot g q lam s r c k.succ - v k • DeltaDot g q lam s r c 0 +
          ε • DeltaDot g q lam s r c 0 := by
      rw [sub_smul]; abel
    rw [this]; exact hε
  obtain ⟨m, f, h, hPz, hP0, hPdeg⟩ := SSKAux.rankdrop_poly _ _ _ hRD
  exact ⟨m, f, h, hPz, hP0, hPdeg⟩
