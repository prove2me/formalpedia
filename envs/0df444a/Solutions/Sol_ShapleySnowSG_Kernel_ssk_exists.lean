-- Prove2me | solution 1 for ShapleySnowSG.Kernel.ssk_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T22:11:39.232086+00:00
-- url     : https://prove2.me/submissions/98670d24-e7fc-4662-8eea-05b73a9253d7

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_MatrixGame
import Theorems.Thm_MatousekLP_ZeroSum_minimax_equality

open Matrix

namespace SSKAux
open ShapleySnowSG.Kernel

lemma onesMat_eq {m : Type*} [Fintype m] (w : ℝ) :
    w • onesMat m m = replicateCol Unit (fun _ => w) * replicateRow Unit (fun _ => (1 : ℝ)) := by
  ext i j
  simp [onesMat, replicateCol, replicateRow, Matrix.mul_apply]

lemma B1_inv {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℝ) (hA : A.det ≠ 0) (w : ℝ) :
    (A + w • onesMat m m).det = A.det + w * Ssum (co A) := by
  rw [onesMat_eq, det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.mpr hA),
    Matrix.det_unique (n := Unit), inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateRow_apply,
    replicateCol_apply, Matrix.smul_apply, smul_eq_mul, one_mul, Ssum, co, transpose_apply,
    Finset.univ_unique, Finset.sum_singleton]
  simp only [Finset.sum_mul, mul_add, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  field_simp

lemma B1_i {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) (w : ℝ) :
    (M + w • onesMat m m).det = M.det + w * Ssum (co M) := by
  let A : ℝ → Matrix m m ℝ := fun t => M + t • (1 : Matrix m m ℝ)
  have hA : ∀ t, (A t).det = (-M).charpoly.eval t := by
    intro t
    rw [eval_charpoly, sub_neg_eq_add, add_comm]
    simp [A, Matrix.scalar_apply, smul_one_eq_diagonal]
  have hfin : {t : ℝ | ((-M).charpoly).IsRoot t}.Finite :=
    Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic _).ne_zero
  have hdense : Dense {t : ℝ | ((-M).charpoly).IsRoot t}ᶜ := hfin.countable.dense_compl ℝ
  have hcA : Continuous A := continuous_const.add (continuous_id.smul continuous_const)
  let g : ℝ → ℝ := fun t => (A t + w • onesMat m m).det - (A t).det - w * Ssum (co (A t))
  have hg : Continuous g := by
    refine ((hcA.add continuous_const).matrix_det.sub hcA.matrix_det).sub
      (continuous_const.mul ?_)
    simp only [Ssum, co, transpose_apply]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact hcA.matrix_adjugate.matrix_elem _ _
  have heq : g = fun _ => 0 := by
    refine Continuous.ext_on hdense hg continuous_const fun t ht => ?_
    have hne : (A t).det ≠ 0 := by
      rw [hA]; exact ht
    simp only [g, B1_inv (A t) hne w]
    ring
  have h0 := congrFun heq 0
  simp only [g, A, zero_smul, add_zero] at h0
  linarith

lemma B1_iii_row {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) (l : m) :
    (co M *ᵥ fun _ => (1 : ℝ)) l = (M.updateRow l (fun _ => 1)).det := by
  rw [det_eq_sum_mul_adjugate_row _ l]
  simp only [mulVec, dotProduct, co, transpose_apply, mul_one, updateRow_self, one_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [adjugate_apply, adjugate_apply, updateRow_idem]

lemma B1_iii {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) (w : ℝ) :
    co (M + w • onesMat m m) *ᵥ (fun _ => (1 : ℝ)) = co M *ᵥ (fun _ => (1 : ℝ)) := by
  ext l
  rw [B1_iii_row, B1_iii_row]
  let u : m → ℝ := fun i => if i = l then 0 else 1
  let v : m → ℝ := w • Pi.single l 1
  have hL : (1 + replicateCol Unit u * replicateRow Unit v).det = 1 := by
    rw [det_one_add_replicateCol_mul_replicateRow, add_eq_left]
    refine Finset.sum_eq_zero fun x _ => ?_
    simp only [v, u, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have hprod : (M + w • onesMat m m).updateRow l (fun _ => 1) =
      (1 + replicateCol Unit u * replicateRow Unit v) * M.updateRow l (fun _ => 1) := by
    have hcv : ∀ i j, (replicateCol Unit u * replicateRow Unit v * M.updateRow l (fun _ => 1)) i j
        = u i * w := by
      intro i j
      rw [Matrix.mul_assoc]
      simp only [Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Finset.univ_unique,
        Finset.sum_singleton, v, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
        mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, updateRow_self]
    ext i j
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, hcv]
    by_cases hi : i = l
    · subst hi
      simp [u, updateRow_self]
    · simp [updateRow_ne hi, u, hi, onesMat]
  rw [hprod, det_mul, hL, one_mul]

end SSKAux

namespace SSKAux
open ShapleySnowSG.Kernel in
theorem B1_full {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) :
    (∀ w : ℝ, (M + w • onesMat m m).det = M.det + w * Ssum (co M)) ∧
    (∀ w : ℝ, Ssum (co (M + w • onesMat m m)) = Ssum (co M)) ∧
    (∀ w : ℝ, co (M + w • onesMat m m) *ᵥ (fun _ => (1 : ℝ)) = co M *ᵥ (fun _ => (1 : ℝ))) ∧
    (∀ w : ℝ, (co (M + w • onesMat m m))ᵀ *ᵥ (fun _ => (1 : ℝ)) =
      (co M)ᵀ *ᵥ (fun _ => (1 : ℝ))) := by
  refine ⟨SSKAux.B1_i M, fun w => ?_, SSKAux.B1_iii M, fun w => ?_⟩
  · rcases eq_or_ne w 0 with hw | hw
    · subst hw; simp
    · have h1 := SSKAux.B1_i M w
      have h2 := SSKAux.B1_i (M + w • onesMat m m) (-w)
      have h3 : M + w • onesMat m m + (-w) • onesMat m m = M := by
        rw [neg_smul, add_neg_cancel_right]
      rw [h3, h1] at h2
      have : w * (Ssum (co M) - Ssum (co (M + w • onesMat m m))) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hw
      · linarith
  · have hT : ∀ N : Matrix m m ℝ, (co N)ᵀ = co Nᵀ := fun N => by
      simp [co, adjugate_transpose]
    have hU : (M + w • onesMat m m)ᵀ = Mᵀ + w • onesMat m m := by
      ext i j; simp [onesMat]
    rw [hT, hT, hU]
    exact SSKAux.B1_iii Mᵀ w

end SSKAux


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

namespace SSKAux
open ShapleySnowSG.Kernel in
theorem B3_core {a : ℕ} (ha : 0 < a) (M : Matrix (Fin a) (Fin a) ℝ) (hrank : M.rank = a - 1)
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

end SSKAux

namespace SSKAux
open ShapleySnowSG.Kernel

lemma shift_row {ι κ : Type*} [Fintype ι] [Fintype κ] (G : Matrix ι κ ℝ) (w : ℝ) (x : ι → ℝ)
    (hx : x ∈ stdSimplex ℝ ι) (j : κ) :
    ∑ i, x i * (G + w • onesMat ι κ) i j = ∑ i, x i * G i j + w := by
  simp only [Matrix.add_apply, Matrix.smul_apply, onesMat, Matrix.of_apply, smul_eq_mul, mul_one,
    mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hx.2, one_mul]

lemma shift_col {ι κ : Type*} [Fintype ι] [Fintype κ] (G : Matrix ι κ ℝ) (w : ℝ) (y : κ → ℝ)
    (hy : y ∈ stdSimplex ℝ κ) (i : ι) :
    ∑ j, (G + w • onesMat ι κ) i j * y j = ∑ j, G i j * y j + w := by
  simp only [Matrix.add_apply, Matrix.smul_apply, onesMat, Matrix.of_apply, smul_eq_mul, mul_one,
    add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hy.2]

lemma isMatVal_shift {ι κ : Type*} [Fintype ι] [Fintype κ] (G : Matrix ι κ ℝ) (v w : ℝ)
    (h : IsMatVal G v) : IsMatVal (G + w • onesMat ι κ) (v + w) := by
  obtain ⟨x, hx, y, hy, h1, h2⟩ := h
  refine ⟨x, hx, y, hy, fun j => ?_, fun i => ?_⟩
  · rw [shift_row G w x hx]; linarith [h1 j]
  · rw [shift_col G w y hy]; linarith [h2 i]

lemma subGame_shift {ι κ : Type*} (G : Matrix ι κ ℝ) (s : ℕ) (r : Fin s ↪ ι) (c : Fin s ↪ κ)
    (w : ℝ) : subGame (G + w • onesMat ι κ) s r c = subGame G s r c + w • onesMat (Fin s) (Fin s) := by
  ext a b; simp [subGame, onesMat]

lemma ssRow_shift {ι κ : Type*} (G : Matrix ι κ ℝ) (s : ℕ) (r : Fin s ↪ ι) (c : Fin s ↪ κ)
    (w : ℝ) : ssRow (G + w • onesMat ι κ) s r c = ssRow G s r c := by
  funext a
  simp only [ssRow]
  rw [subGame_shift, (B1_full _).2.2.1, (B1_full _).2.1]

lemma ssCol_shift {ι κ : Type*} (G : Matrix ι κ ℝ) (s : ℕ) (r : Fin s ↪ ι) (c : Fin s ↪ κ)
    (w : ℝ) : ssCol (G + w • onesMat ι κ) s r c = ssCol G s r c := by
  funext a
  simp only [ssCol]
  rw [subGame_shift, (B1_full _).2.2.2, (B1_full _).2.1]

lemma B2_core {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : Matrix ι κ ℝ) (s : ℕ) (r : Fin s ↪ ι) (c : Fin s ↪ κ) (hK : IsSSK G s r c) (w : ℝ) :
    IsSSK (G + w • onesMat ι κ) s r c := by
  obtain ⟨hS, ⟨hxs, w1, hw1, hx1⟩, ⟨hys, w2, hw2, hy2⟩⟩ := hK
  have hpr : padRow (G + w • onesMat ι κ) s r c = padRow G s r c := by
    simp only [padRow, ssRow_shift]
  have hpc : padCol (G + w • onesMat ι κ) s r c = padCol G s r c := by
    simp only [padCol, ssCol_shift]
  refine ⟨?_, ?_, ?_⟩
  · rw [subGame_shift, (B1_full _).2.1]; exact hS
  · rw [hpr]
    refine ⟨hxs, w1 + w, isMatVal_shift G w1 w hw1, fun j => ?_⟩
    rw [shift_row G w _ hxs]; linarith [hx1 j]
  · rw [hpc]
    refine ⟨hys, w2 + w, isMatVal_shift G w2 w hw2, fun i => ?_⟩
    rw [shift_col G w _ hys]; linarith [hy2 i]

lemma ker_eq_span {s : ℕ} (N : Matrix (Fin s) (Fin s) ℝ) (hadj : N.adjugate ≠ 0) (y : Fin s → ℝ)
    (hy0 : y ≠ 0) (hy : N *ᵥ y = 0) :
    LinearMap.ker N.mulVecLin = ℝ ∙ y ∧ N.rank = s - 1 := by
  cases s with
  | zero => exact absurd (Subsingleton.elim y 0) hy0
  | succ n =>
    obtain ⟨i, j, hij⟩ : ∃ i j, N.adjugate i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hadj (Matrix.ext h)
    rw [adjugate_fin_succ_eq_det_submatrix] at hij
    have hdet : (N.submatrix j.succAbove i.succAbove).det ≠ 0 := fun h0 => hij (by rw [h0, mul_zero])
    have h1 := rank_of_det_ne_zero hdet
    have h2 := rank_submatrix_le N j.succAbove i.succAbove
    rw [Fintype.card_fin] at h1
    have hrn := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    rw [Module.finrank_fin_fun] at hrn
    have hle : ℝ ∙ y ≤ LinearMap.ker N.mulVecLin :=
      (Submodule.span_singleton_le_iff_mem _ _).mpr (by rw [LinearMap.mem_ker, mulVecLin_apply, hy])
    have hfy : Module.finrank ℝ (ℝ ∙ y) = 1 := finrank_span_singleton hy0
    have hmono := Submodule.finrank_mono hle
    have hrk : N.rank = Module.finrank ℝ (LinearMap.range N.mulVecLin) := rfl
    have hker : Module.finrank ℝ (LinearMap.ker N.mulVecLin) = 1 := by omega
    refine ⟨(Submodule.eq_of_le_of_finrank_eq hle (by rw [hfy, hker])).symm, ?_⟩
    omega

end SSKAux

open Matrix

namespace SSKAux
open ShapleySnowSG.Kernel

lemma exists_val_fin {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (M : Matrix (Fin m) (Fin n) ℝ) :
    ∃ w, IsMatVal M w := by
  obtain ⟨v, ⟨⟨x, hx, hxv⟩, _⟩, ⟨⟨y, hy, hyv⟩, _⟩⟩ := MatousekLP.ZeroSum.minimax_equality hm hn M
  refine ⟨v, x, hx, y, hy, fun j => ?_, fun i => ?_⟩
  · have hc : Continuous fun y' : Fin n → ℝ => MatousekLP.ZeroSum.payoff M x y' :=
      continuous_const.dotProduct (continuous_const.matrix_mulVec continuous_id)
    have hbdd := ((isCompact_stdSimplex ℝ (Fin n)).image hc).bddBelow
    have := csInf_le hbdd ⟨Pi.single j 1, single_mem_stdSimplex ℝ j, rfl⟩
    rw [← hxv]
    refine this.trans (le_of_eq ?_)
    simp only [MatousekLP.ZeroSum.payoff, mulVec_single_one, dotProduct, col_apply]
  · have hc : Continuous fun x' : Fin m → ℝ => MatousekLP.ZeroSum.payoff M x' y :=
      continuous_id.dotProduct continuous_const
    have hbdd := ((isCompact_stdSimplex ℝ (Fin m)).image hc).bddAbove
    have := le_csSup hbdd ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, rfl⟩
    rw [← hyv]
    refine (le_of_eq ?_).trans this
    simp [MatousekLP.ZeroSum.payoff, Pi.single_apply, mulVec, dotProduct]

lemma exists_val {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (A : Matrix ι κ ℝ) : ∃ w, IsMatVal A w := by
  classical
  let e1 := Fintype.equivFin ι
  let e2 := Fintype.equivFin κ
  obtain ⟨w, x, hx, y, hy, h1, h2⟩ := exists_val_fin (Fintype.card_pos (α := ι))
    (Fintype.card_pos (α := κ)) (A.submatrix e1.symm e2.symm)
  refine ⟨w, x ∘ e1, ⟨fun i => hx.1 _, ?_⟩, y ∘ e2, ⟨fun j => hy.1 _, ?_⟩, fun j => ?_, fun i => ?_⟩
  · rw [← hx.2]; exact Equiv.sum_comp e1 x
  · rw [← hy.2]; exact Equiv.sum_comp e2 y
  · have := h1 (e2 j)
    rw [← Equiv.sum_comp e1] at this
    simpa using this
  · have := h2 (e1 i)
    rw [← Equiv.sum_comp e2] at this
    simpa using this

end SSKAux

open Matrix

namespace SSKAux

lemma max_indep {α V : Type*} [Fintype α] [DecidableEq α] [AddCommGroup V] [Module ℝ V]
    (v : α → V) (S : Finset α) (hS : LinearIndepOn ℝ v (S : Set α)) :
    ∃ R : Finset α, S ⊆ R ∧ LinearIndepOn ℝ v (R : Set α) ∧
      ∀ i, ∃ c : R → ℝ, ∑ r, c r • v r = v i := by
  classical
  let F := (Finset.univ : Finset (Finset α)).filter (fun R => S ⊆ R ∧ LinearIndepOn ℝ v (R : Set α))
  obtain ⟨R, hRF, hmax⟩ := F.exists_max_image Finset.card ⟨S, by simp [F, hS]⟩
  simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hRF
  refine ⟨R, hRF.1, hRF.2, fun i => ?_⟩
  have hspan : v i ∈ Submodule.span ℝ (v '' (R : Set α)) := by
    by_contra h
    have hi : i ∉ R := fun hi => h (Submodule.subset_span ⟨i, hi, rfl⟩)
    have hins : insert i R ∈ F := by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_insert]
      exact ⟨hRF.1.trans (Finset.subset_insert _ _), hRF.2.insert h⟩
    have := hmax _ hins
    rw [Finset.card_insert_of_notMem hi] at this
    omega
  rw [Set.image_eq_range] at hspan
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan

lemma exists_square_nonsing {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (N : Matrix α β ℝ) (S : Finset α) (T : Finset β)
    (hS : LinearIndepOn ℝ N.row (S : Set α)) (hT : LinearIndepOn ℝ N.col (T : Set β)) :
    ∃ (m : ℕ) (f : Fin m ↪ α) (g : Fin m ↪ β), (∀ i ∈ S, ∃ a, f a = i) ∧
      (∀ j ∈ T, ∃ b, g b = j) ∧ (N.submatrix f g).det ≠ 0 := by
  obtain ⟨R, hSR, hR, hRspan⟩ := max_indep N.row S hS
  obtain ⟨C, hTC, hC, hCspan⟩ := max_indep N.col T hT
  -- a combination of the columns in `C` that vanishes on the rows `R` vanishes everywhere
  have hrowext : ∀ (a : C → ℝ), (∀ r : R, ∑ c, a c * N r c = 0) → ∀ i, ∑ c, a c * N i c = 0 := by
    intro a ha i
    obtain ⟨l, hl⟩ := hRspan i
    have : ∀ c : C, N i c = ∑ r, l r * N r c := fun c => by
      have := congrFun hl c
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row] at this
      exact this.symm
    simp_rw [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun r _ => ?_
    have := ha r
    calc ∑ c, a c * (l r * N r c) = l r * ∑ c, a c * N r c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
      _ = 0 := by rw [this, mul_zero]
  have hcolext : ∀ (b : R → ℝ), (∀ c : C, ∑ r, b r * N r c = 0) → ∀ j, ∑ r, b r * N r j = 0 := by
    intro b hb j
    obtain ⟨l, hl⟩ := hCspan j
    have : ∀ r : R, N r j = ∑ c, l c * N r c := fun r => by
      have := congrFun hl r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col, transpose_apply] at this
      exact this.symm
    simp_rw [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c _ => ?_
    have := hb c
    calc ∑ r, b r * (l c * N r c) = l c * ∑ r, b r * N r c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
      _ = 0 := by rw [this, mul_zero]
  -- columns `C` restricted to rows `R` are independent, and vice versa
  have hCR : LinearIndependent ℝ (fun c : C => fun r : R => N r c) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have h1 : ∀ r : R, ∑ c, a c * N r c = 0 := fun r => by
      have := congrFun ha r
      simpa [Finset.sum_apply] using this
    have h2 := hrowext a h1
    have hC' : LinearIndependent ℝ (fun c : C => N.col c) := hC
    rw [Fintype.linearIndependent_iff] at hC'
    exact hC' a (funext fun i => by simpa [Finset.sum_apply, Matrix.col] using h2 i)
  have hRC : LinearIndependent ℝ (fun r : R => fun c : C => N r c) := by
    rw [Fintype.linearIndependent_iff]
    intro b hb
    have h1 : ∀ c : C, ∑ r, b r * N r c = 0 := fun c => by
      have := congrFun hb c
      simpa [Finset.sum_apply] using this
    have h2 := hcolext b h1
    have hR' : LinearIndependent ℝ (fun r : R => N.row r) := hR
    rw [Fintype.linearIndependent_iff] at hR'
    exact hR' b (funext fun j => by simpa [Finset.sum_apply, Matrix.row] using h2 j)
  have hc1 := hCR.fintype_card_le_finrank
  have hc2 := hRC.fintype_card_le_finrank
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hc1 hc2
  have hcard : C.card = R.card := le_antisymm hc1 hc2
  let eR : Fin R.card ≃ R := R.equivFin.symm
  let eC : Fin R.card ≃ C := (finCongr hcard.symm).trans C.equivFin.symm
  let f : Fin R.card ↪ α := ⟨fun a => (eR a : α), fun a b h => eR.injective (Subtype.ext h)⟩
  let g : Fin R.card ↪ β := ⟨fun a => (eC a : β), fun a b h => eC.injective (Subtype.ext h)⟩
  refine ⟨R.card, f, g, fun i hi => ⟨eR.symm ⟨i, hSR hi⟩, by
      show ((eR (eR.symm ⟨i, hSR hi⟩) : R) : α) = i
      rw [Equiv.apply_symm_apply]⟩,
    fun j hj => ⟨eC.symm ⟨j, hTC hj⟩, by
      show ((eC (eC.symm ⟨j, hTC hj⟩) : C) : β) = j
      rw [Equiv.apply_symm_apply]⟩, ?_⟩
  intro hdet
  obtain ⟨a, ha0, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply ha0
  have hCR' := hCR
  rw [Fintype.linearIndependent_iff] at hCR'
  have := hCR' (fun c => a (eC.symm c)) (funext fun r => ?_)
  · funext b
    have h := this (eC b)
    simpa using h
  · have h := congrFun ha (eR.symm r)
    simp only [mulVec, dotProduct, submatrix_apply, Pi.zero_apply] at h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← h]
    rw [← Equiv.sum_comp eC]
    simp only [Equiv.symm_apply_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    show a b * N r (eC b) = N ((eR (eR.symm r) : R) : α) (eC b) * a b
    rw [Equiv.apply_symm_apply, mul_comm]

end SSKAux

namespace SSKAux
open ShapleySnowSG.Kernel

lemma sum_eq_of_extend {ι : Type*} [Fintype ι] {s : ℕ} (r : Fin s ↪ ι) (x : ι → ℝ)
    (hx : ∀ i, (∀ a, r a ≠ i) → x i = 0) (φ : ι → ℝ) :
    ∑ i, x i * φ i = ∑ a, x (r a) * φ (r a) := by
  have hext : x = Function.extend r (fun a => x (r a)) 0 := by
    funext i
    by_cases h : ∃ a, r a = i
    · obtain ⟨a, rfl⟩ := h
      rw [r.injective.extend_apply]
    · push Not at h
      rw [Function.extend_apply' _ _ _ (by rintro ⟨a, ha⟩; exact h a ha), hx i h]
      rfl
  conv_lhs => rw [hext]
  exact sum_extend_mul r _ φ

lemma ssk_exists_one {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (H : Matrix ι κ ℝ) (hval : IsMatVal H 1) : ∃ (s : ℕ) (r : Fin s ↪ ι) (c : Fin s ↪ κ),
    IsSSK H s r c := by
  let X1 : Set (ι → ℝ) := stdSimplex ℝ ι ∩ {x | ∀ j, 1 ≤ ∑ i, x i * H i j}
  let Y1 : Set (κ → ℝ) := stdSimplex ℝ κ ∩ {y | ∀ i, ∑ j, H i j * y j ≤ 1}
  have hX1c : IsCompact X1 := (isCompact_stdSimplex ℝ ι).inter_right (by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const
      (continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const))
  have hY1c : IsCompact Y1 := (isCompact_stdSimplex ℝ κ).inter_right (by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le
      (continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_apply j)) continuous_const)
  obtain ⟨x0, hx0, y0, hy0, h01, h02⟩ := hval
  obtain ⟨x, hxext⟩ := hX1c.extremePoints_nonempty ⟨x0, hx0, h01⟩
  obtain ⟨y, hyext⟩ := hY1c.extremePoints_nonempty ⟨y0, hy0, h02⟩
  rw [mem_extremePoints] at hxext hyext
  obtain ⟨⟨hxS, hxH⟩, hxe⟩ := hxext
  obtain ⟨⟨hyS, hyH⟩, hye⟩ := hyext
  -- complementary slackness
  have hP : ∑ i, x i * ∑ j, H i j * y j = ∑ j, (∑ i, x i * H i j) * y j := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hA : ∑ i, x i * (1 - ∑ j, H i j * y j) = 1 - ∑ i, x i * ∑ j, H i j * y j := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hxS.2]
  have hB : ∑ j, ((∑ i, x i * H i j) - 1) * y j = ∑ j, (∑ i, x i * H i j) * y j - 1 := by
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, hyS.2]
  have hA0 : 0 ≤ ∑ i, x i * (1 - ∑ j, H i j * y j) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hxS.1 i) (by linarith [hyH i])
  have hB0 : 0 ≤ ∑ j, ((∑ i, x i * H i j) - 1) * y j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (by linarith [hxH j]) (hyS.1 j)
  have hA1 : ∑ i, x i * (1 - ∑ j, H i j * y j) = 0 := by linarith
  have hB1 : ∑ j, ((∑ i, x i * H i j) - 1) * y j = 0 := by linarith
  have hcs1 : ∀ i, 0 < x i → ∑ j, H i j * y j = 1 := by
    intro i hi
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hxS.1 i)
      (by linarith [hyH i]))).mp hA1 i (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have hcs2 : ∀ j, 0 < y j → ∑ i, x i * H i j = 1 := by
    intro j hj
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (by linarith [hxH j])
      (hyS.1 j))).mp hB1 j (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  -- perturbation lemmas
  have hpy : ∀ c : κ → ℝ, (∀ j, y j = 0 → c j = 0) →
      (∀ i, ∑ j, H i j * y j = 1 → ∑ j, H i j * c j = 0) → ∑ j, c j = 0 → c = 0 := by
    intro c hc1 hc2 hc3
    have hev : ∀ᶠ ε in nhds (0 : ℝ), y + ε • c ∈ Y1 := by
      have e1 : ∀ᶠ ε in nhds (0 : ℝ), ∀ j, 0 ≤ (y + ε • c) j := by
        rw [Filter.eventually_all]
        intro j
        by_cases hyj : y j = 0
        · exact Filter.Eventually.of_forall fun ε => by simp [hyj, hc1 j hyj]
        · have hpos : 0 < y j := lt_of_le_of_ne (hyS.1 j) (Ne.symm hyj)
          have hcf : Continuous (fun ε : ℝ => y j + ε * c j) := by fun_prop
          have ht := hcf.tendsto' 0 (y j) (by simp)
          exact (ht.eventually_const_lt hpos).mono fun ε h => by simp; linarith
      have e2 : ∀ᶠ ε in nhds (0 : ℝ), ∀ i, ∑ j, H i j * (y + ε • c) j ≤ 1 := by
        rw [Filter.eventually_all]
        intro i
        have hsum : ∀ ε : ℝ, ∑ j, H i j * (y + ε • c) j =
            ∑ j, H i j * y j + ε * ∑ j, H i j * c j := fun ε => by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
            Finset.mul_sum]
          congr 1; exact Finset.sum_congr rfl fun j _ => by ring
        by_cases hi : ∑ j, H i j * y j = 1
        · exact Filter.Eventually.of_forall fun ε => by rw [hsum, hi, hc2 i hi]; simp
        · have hlt : ∑ j, H i j * y j < 1 := lt_of_le_of_ne (hyH i) hi
          have hcf : Continuous (fun ε : ℝ => ∑ j, H i j * y j + ε * ∑ j, H i j * c j) := by fun_prop
          have ht := hcf.tendsto' 0 (∑ j, H i j * y j) (by simp)
          exact (ht.eventually_lt_const hlt).mono fun ε h => by rw [hsum]; exact h.le
      filter_upwards [e1, e2] with ε h1 h2
      refine ⟨⟨h1, ?_⟩, h2⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
        hyS.2, hc3, mul_zero, add_zero]
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have hp := hball (y := δ / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
    have hm := hball (y := -(δ / 2)) (by
      rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith)
    have hseg : y ∈ openSegment ℝ (y + (δ / 2) • c) (y + (-(δ / 2)) • c) :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
        funext j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring⟩
    have := (hye _ hp _ hm hseg).1
    funext j
    have hj := congrFun this j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj
    have : δ / 2 * c j = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · simpa using h
  have hpx : ∀ d : ι → ℝ, (∀ i, x i = 0 → d i = 0) →
      (∀ j, ∑ i, x i * H i j = 1 → ∑ i, d i * H i j = 0) → ∑ i, d i = 0 → d = 0 := by
    intro d hd1 hd2 hd3
    have hev : ∀ᶠ ε in nhds (0 : ℝ), x + ε • d ∈ X1 := by
      have e1 : ∀ᶠ ε in nhds (0 : ℝ), ∀ i, 0 ≤ (x + ε • d) i := by
        rw [Filter.eventually_all]
        intro i
        by_cases hxi : x i = 0
        · exact Filter.Eventually.of_forall fun ε => by simp [hxi, hd1 i hxi]
        · have hpos : 0 < x i := lt_of_le_of_ne (hxS.1 i) (Ne.symm hxi)
          have hcf : Continuous (fun ε : ℝ => x i + ε * d i) := by fun_prop
          have ht := hcf.tendsto' 0 (x i) (by simp)
          exact (ht.eventually_const_lt hpos).mono fun ε h => by simp; linarith
      have e2 : ∀ᶠ ε in nhds (0 : ℝ), ∀ j, 1 ≤ ∑ i, (x + ε • d) i * H i j := by
        rw [Filter.eventually_all]
        intro j
        have hsum : ∀ ε : ℝ, ∑ i, (x + ε • d) i * H i j =
            ∑ i, x i * H i j + ε * ∑ i, d i * H i j := fun ε => by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
            Finset.mul_sum]
          congr 1; exact Finset.sum_congr rfl fun i _ => by ring
        by_cases hj : ∑ i, x i * H i j = 1
        · exact Filter.Eventually.of_forall fun ε => by rw [hsum, hj, hd2 j hj]; simp
        · have hlt : 1 < ∑ i, x i * H i j := lt_of_le_of_ne (hxH j) (Ne.symm hj)
          have hcf : Continuous (fun ε : ℝ => ∑ i, x i * H i j + ε * ∑ i, d i * H i j) := by fun_prop
          have ht := hcf.tendsto' 0 (∑ i, x i * H i j) (by simp)
          exact (ht.eventually_const_lt hlt).mono fun ε h => by rw [hsum]; exact h.le
      filter_upwards [e1, e2] with ε h1 h2
      refine ⟨⟨h1, ?_⟩, h2⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
        hxS.2, hd3, mul_zero, add_zero]
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have hp := hball (y := δ / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
    have hm := hball (y := -(δ / 2)) (by
      rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith)
    have hseg : x ∈ openSegment ℝ (x + (δ / 2) • d) (x + (-(δ / 2)) • d) :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
        funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring⟩
    have := (hxe _ hp _ hm hseg).1
    funext i
    have hi := congrFun this i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    have : δ / 2 * d i = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · simpa using h
  classical
  have hval1 : IsMatVal H 1 := ⟨x, hxS, y, hyS, hxH, hyH⟩
  let I1 := {i : ι // ∑ j, H i j * y j = 1}
  let J1 := {j : κ // ∑ i, x i * H i j = 1}
  let N : Matrix I1 J1 ℝ := fun i j => H i.1 j.1
  let S : Finset I1 := Finset.univ.filter (fun i => 0 < x i.1)
  let T : Finset J1 := Finset.univ.filter (fun j => 0 < y j.1)
  have hT : LinearIndepOn ℝ N.col (T : Set J1) := by
    show LinearIndependent ℝ (fun t : (T : Set J1) => N.col t)
    rw [Fintype.linearIndependent_iff]
    intro g hg
    let c : κ → ℝ := fun j => ∑ t : (T : Set J1), if (t : J1).1 = j then g t else 0
    have hcsum : ∀ (φ : κ → ℝ), ∑ j, φ j * c j = ∑ t : (T : Set J1), g t * φ (t : J1).1 := by
      intro φ
      simp only [c, Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.sum_ite_eq]
      simp [mul_comm]
    have hcN : ∀ i : I1, ∑ t : (T : Set J1), g t * H i.1 (t : J1).1 = 0 := by
      intro i
      have := congrFun hg i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      exact this
    have hc0 := hpy c ?_ ?_ ?_
    · intro t
      have := congrFun hc0 (t : J1).1
      simp only [c, Pi.zero_apply] at this
      rw [Finset.sum_eq_single t (fun t' _ ht' => by
        rw [if_neg]; intro h; exact ht' (Subtype.ext (Subtype.ext h))) (by simp)] at this
      simpa using this
    · intro j hj
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [if_neg]
      intro h
      have ht := t.2
      simp only [T, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
      rw [h, hj] at ht
      exact lt_irrefl _ ht
    · intro i hi
      rw [hcsum (fun j => H i j)]
      exact hcN ⟨i, hi⟩
    · have h1 : ∑ j, c j = ∑ t, g t := by
        have := hcsum (fun _ => 1)
        simpa using this
      rw [h1]
      have : ∑ t : (T : Set J1), g t =
          ∑ i, x i * ∑ t : (T : Set J1), g t * H i (t : J1).1 := by
        have e : ∑ i, x i * ∑ t : (T : Set J1), g t * H i (t : J1).1 =
            ∑ t : (T : Set J1), g t * ∑ i, x i * H i (t : J1).1 := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        rw [e]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [(t : J1).2, mul_one]
      rw [this]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hxi : x i = 0
      · simp [hxi]
      · have hpos : 0 < x i := lt_of_le_of_ne (hxS.1 i) (Ne.symm hxi)
        rw [hcN ⟨i, hcs1 i hpos⟩, mul_zero]
  have hS : LinearIndepOn ℝ N.row (S : Set I1) := by
    show LinearIndependent ℝ (fun t : (S : Set I1) => N.row t)
    rw [Fintype.linearIndependent_iff]
    intro g hg
    let d : ι → ℝ := fun i => ∑ t : (S : Set I1), if (t : I1).1 = i then g t else 0
    have hdsum : ∀ (φ : ι → ℝ), ∑ i, d i * φ i = ∑ t : (S : Set I1), g t * φ (t : I1).1 := by
      intro φ
      simp only [d, Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.sum_ite_eq]
      simp
    have hdN : ∀ j : J1, ∑ t : (S : Set I1), g t * H (t : I1).1 j.1 = 0 := by
      intro j
      have := congrFun hg j
      simpa [Finset.sum_apply, Matrix.row, N] using this
    have hd0 := hpx d ?_ ?_ ?_
    · intro t
      have := congrFun hd0 (t : I1).1
      simp only [d, Pi.zero_apply] at this
      rw [Finset.sum_eq_single t (fun t' _ ht' => by
        rw [if_neg]; intro h; exact ht' (Subtype.ext (Subtype.ext h))) (by simp)] at this
      simpa using this
    · intro i hi
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [if_neg]
      intro h
      have ht := t.2
      simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
      rw [h, hi] at ht
      exact lt_irrefl _ ht
    · intro j hj
      rw [hdsum (fun i => H i j)]
      exact hdN ⟨j, hj⟩
    · have h1 : ∑ i, d i = ∑ t, g t := by
        have := hdsum (fun _ => 1)
        simpa using this
      rw [h1]
      have : ∑ t : (S : Set I1), g t =
          ∑ j, (∑ t : (S : Set I1), g t * H (t : I1).1 j) * y j := by
        have e : ∑ j, (∑ t : (S : Set I1), g t * H (t : I1).1 j) * y j =
            ∑ t : (S : Set I1), g t * ∑ j, H (t : I1).1 j * y j := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        rw [e]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [(t : I1).2, mul_one]
      rw [this]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hyj : y j = 0
      · simp [hyj]
      · have hpos : 0 < y j := lt_of_le_of_ne (hyS.1 j) (Ne.symm hyj)
        rw [hdN ⟨j, hcs2 j hpos⟩, zero_mul]
  obtain ⟨m, f, g, hSf, hTg, hdet⟩ := exists_square_nonsing N S T hS hT
  let r : Fin m ↪ ι := f.trans (Function.Embedding.subtype _)
  let c : Fin m ↪ κ := g.trans (Function.Embedding.subtype _)
  have hysupp : ∀ j, (∀ b, c b ≠ j) → y j = 0 := by
    intro j hj
    by_contra hne
    have hpos : 0 < y j := lt_of_le_of_ne (hyS.1 j) (Ne.symm hne)
    obtain ⟨b, hb⟩ := hTg ⟨j, hcs2 j hpos⟩ (by simp [T, hpos])
    exact hj b (by show ((g b : J1) : κ) = j; rw [hb])
  have hxsupp : ∀ i, (∀ a, r a ≠ i) → x i = 0 := by
    intro i hi
    by_contra hne
    have hpos : 0 < x i := lt_of_le_of_ne (hxS.1 i) (Ne.symm hne)
    obtain ⟨a, ha⟩ := hSf ⟨i, hcs1 i hpos⟩ (by simp [S, hpos])
    exact hi a (by show ((f a : I1) : ι) = i; rw [ha])
  set D := subGame H m r c with hD
  have hdetD : D.det ≠ 0 := hdet
  let yC : Fin m → ℝ := fun b => y (c b)
  let xR : Fin m → ℝ := fun a => x (r a)
  have hHy : D *ᵥ yC = fun _ => 1 := by
    funext a
    have h := sum_eq_of_extend c y hysupp (fun j => H (r a) j)
    have h1 : ∑ j, H (r a) j * y j = 1 := (f a).2
    simp only [mulVec, dotProduct, hD, subGame, submatrix_apply, yC]
    rw [← h1]
    simp_rw [mul_comm (H _ _)]
    exact h.symm
  have hxH' : xR ᵥ* D = fun _ => 1 := by
    funext b
    have h := sum_eq_of_extend r x hxsupp (fun i => H i (c b))
    have h1 : ∑ i, x i * H i (c b) = 1 := (g b).2
    simp only [vecMul, dotProduct, hD, subGame, submatrix_apply, xR]
    rw [← h1]
    exact h.symm
  have hysum : ∑ b, yC b = 1 := by
    have := sum_eq_of_extend c y hysupp (fun _ => 1)
    simp only [mul_one] at this
    rw [← hyS.2, this]
  have hxsum : ∑ a, xR a = 1 := by
    have := sum_eq_of_extend r x hxsupp (fun _ => 1)
    simp only [mul_one] at this
    rw [← hxS.2, this]
  have hadjy : D.adjugate *ᵥ (fun _ => (1 : ℝ)) = D.det • yC := by
    rw [← hHy, mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  have hadjx : (fun _ => (1 : ℝ)) ᵥ* D.adjugate = D.det • xR := by
    rw [← hxH', vecMul_vecMul, mul_adjugate, vecMul_smul, vecMul_one]
  have hSD : Ssum (co D) = D.det := by
    simp only [Ssum, co, transpose_apply]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ a, D.adjugate b a = D.det * yC b := fun b => by
      have := congrFun hadjy b
      simpa [mulVec, dotProduct] using this
    simp_rw [this, ← Finset.mul_sum, hysum, mul_one]
  have hcol : ssCol H m r c = yC := by
    funext b
    show ((co D)ᵀ *ᵥ fun _ => (1 : ℝ)) b / Ssum (co D) = yC b
    rw [hSD, co, transpose_transpose, hadjy, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hrow : ssRow H m r c = xR := by
    funext a
    show (co D *ᵥ fun _ => (1 : ℝ)) a / Ssum (co D) = xR a
    rw [hSD, co, mulVec_transpose, hadjx, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hpadR : padRow H m r c = x := by
    funext i
    simp only [padRow, hrow]
    by_cases h : ∃ a, r a = i
    · obtain ⟨a, rfl⟩ := h
      rw [r.injective.extend_apply]
    · push Not at h
      rw [Function.extend_apply' _ _ _ (by rintro ⟨a, ha⟩; exact h a ha), hxsupp i h]
      rfl
  have hpadC : padCol H m r c = y := by
    funext j
    simp only [padCol, hcol]
    by_cases h : ∃ b, c b = j
    · obtain ⟨b, rfl⟩ := h
      rw [c.injective.extend_apply]
    · push Not at h
      rw [Function.extend_apply' _ _ _ (by rintro ⟨b, hb⟩; exact h b hb), hysupp j h]
      rfl
  refine ⟨m, r, c, ?_, ?_, ?_⟩
  · rw [← hD, hSD]; exact hdetD
  · rw [hpadR]; exact ⟨hxS, 1, hval1, hxH⟩
  · rw [hpadC]; exact ⟨hyS, 1, hval1, hyH⟩

lemma ssk_exists_core {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (G : Matrix ι κ ℝ) : ∃ (s : ℕ) (r : Fin s ↪ ι) (c : Fin s ↪ κ), IsSSK G s r c := by
  classical
  obtain ⟨v, hv⟩ := exists_val G
  have h1 : IsMatVal (G + (1 - v) • onesMat ι κ) 1 := by
    have := isMatVal_shift G v (1 - v) hv
    rwa [add_sub_cancel] at this
  obtain ⟨s, r, c, hK⟩ := ssk_exists_one _ h1
  have hK2 := B2_core _ s r c hK (v - 1)
  have e : G + (1 - v) • onesMat ι κ + (v - 1) • onesMat ι κ = G := by
    rw [add_assoc, ← add_smul]; simp
  rw [e] at hK2
  exact ⟨s, r, c, hK2⟩

end SSKAux

open ShapleySnowSG.Kernel in
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (G : Matrix ι κ ℝ) :
    ∃ (s : ℕ) (r : Fin s ↪ ι) (c : Fin s ↪ κ), IsSSK G s r c :=
  SSKAux.ssk_exists_core G
