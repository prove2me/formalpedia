-- Prove2me | solution 1 for ShapleySnowSG.Kernel.prop_2_4_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T21:39:47.158953+00:00
-- url     : https://prove2.me/submissions/6c9735d9-1b48-437d-adb0-c461033171e8

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_KroneckerMEP

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


namespace SSKAux
open ShapleySnowSG.Kernel

lemma aux_transpose {n : ℕ} {p q : Fin n → Type*}
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (q k) ℝ) (ℓ : Fin (n + 1)) :
    aux (fun k l => (M k l)ᵀ) ℓ = (aux M ℓ)ᵀ := by
  ext i j
  rfl

lemma pencil_transpose {n : ℕ} {p q : Fin n → Type*}
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (q k) ℝ) (z : Fin n → ℝ) (k : Fin n) :
    pencil (fun k l => (M k l)ᵀ) z k = (pencil M z k)ᵀ := by
  simp [pencil, transpose_add, transpose_sum, transpose_smul]

end SSKAux
namespace SSKAux
open ShapleySnowSG.Kernel

lemma dot_pos' {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (σ : ℝ) (hB : ∀ a b, 0 < σ * B a b)
    (x y : ι → ℝ) (hx0 : ∀ a, 0 ≤ x a) (hy0 : ∀ b, 0 ≤ y b) (hx1 : ∃ a, 0 < x a)
    (hy1 : ∃ b, 0 < y b) : 0 < σ * (x ⬝ᵥ (B *ᵥ y)) := by
  obtain ⟨a0, ha0⟩ := hx1
  obtain ⟨b0, hb0⟩ := hy1
  have : σ * (x ⬝ᵥ (B *ᵥ y)) = ∑ a, ∑ b, x a * y b * (σ * B a b) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [this]
  refine Finset.sum_pos' (fun a _ => Finset.sum_nonneg fun b _ =>
    mul_nonneg (mul_nonneg (hx0 a) (hy0 b)) (hB a b).le) ⟨a0, Finset.mem_univ _, ?_⟩
  exact Finset.sum_pos' (fun b _ => mul_nonneg (mul_nonneg (hx0 a0) (hy0 b)) (hB a0 b).le)
    ⟨b0, Finset.mem_univ _, mul_pos (mul_pos ha0 hb0) (hB a0 b0)⟩

lemma tensor_pos {n : ℕ} {p : Fin n → Type*} (x : ∀ k, p k → ℝ)
    (hx : ∀ k, 0 ≤ x k ∧ x k ≠ 0) :
    (∀ i, 0 ≤ tensorVec x i) ∧ ∃ i, 0 < tensorVec x i := by
  refine ⟨fun i => Finset.prod_nonneg fun k _ => (hx k).1 _, ?_⟩
  have : ∀ k, ∃ a, 0 < x k a := by
    intro k
    by_contra h
    push Not at h
    exact (hx k).2 (funext fun a => le_antisymm (h a) ((hx k).1 a))
  choose a ha using this
  exact ⟨a, Finset.prod_pos fun k _ => ha k⟩

end SSKAux

open ShapleySnowSG.Kernel in
theorem solution {n : ℕ} {p : Fin n → Type*} [∀ k, Fintype (p k)] [∀ k, DecidableEq (p k)]
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (p k) ℝ)
    (hΔ : (∀ i j, 0 < aux M 0 i j) ∨ (∀ i j, aux M 0 i j < 0))
    (z : Fin n → ℝ) (hz : z ∈ SM M) (x y : ∀ k, p k → ℝ)
    (hx : ∀ k, (pencil M z k)ᵀ *ᵥ x k = 0) (hxpos : ∀ k, 0 ≤ x k ∧ x k ≠ 0)
    (hy : ∀ k, pencil M z k *ᵥ y k = 0) (hypos : ∀ k, 0 ≤ y k ∧ y k ≠ 0) :
    z ∈ SR M := by
  intro k
  have hYk := SSKAux.kron_kernel M z y hy k
  have hXk := SSKAux.kron_kernel (fun k l => (M k l)ᵀ) z x
    (fun k' => by rw [SSKAux.pencil_transpose]; exact hx k') k
  rw [SSKAux.aux_transpose, SSKAux.aux_transpose, ← transpose_smul, ← transpose_sub] at hXk
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, ∀ a b, 0 < σ * aux M 0 a b := by
    rcases hΔ with h | h
    · exact ⟨1, fun a b => by simpa using h a b⟩
    · exact ⟨-1, fun a b => by simpa using h a b⟩
  obtain ⟨hX0, hX1⟩ := SSKAux.tensor_pos x hxpos
  obtain ⟨hY0, hY1⟩ := SSKAux.tensor_pos y hypos
  have hxy : tensorVec x ⬝ᵥ (aux M 0 *ᵥ tensorVec y) ≠ 0 := by
    have := SSKAux.dot_pos' (aux M 0) σ hσ _ _ hX0 hY0 hX1 hY1
    intro h0; rw [h0, mul_zero] at this; exact lt_irrefl _ this
  obtain ⟨ε, hε⟩ := SSKAux.C1_core (aux M k.succ - z k • aux M 0) (aux M 0) (tensorVec x)
    (tensorVec y) hXk hYk hxy
  refine ⟨z k - ε, ?_⟩
  have : aux M k.succ - (z k - ε) • aux M 0 = aux M k.succ - z k • aux M 0 + ε • aux M 0 := by
    rw [sub_smul]; abel
  rw [this]; exact hε
