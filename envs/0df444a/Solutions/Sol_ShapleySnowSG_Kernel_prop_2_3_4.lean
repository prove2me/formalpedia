-- Prove2me | solution 1 for ShapleySnowSG.Kernel.prop_2_3_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T21:50:15.659434+00:00
-- url     : https://prove2.me/submissions/8a22229a-7282-405b-9b17-f5780dbe2e62

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_MatrixGame

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

open ShapleySnowSG.Kernel in
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (G : Matrix ι κ ℝ) (v : ℝ) (hv : IsMatVal G v)
    (s : ℕ) (r : Fin s ↪ ι) (c : Fin s ↪ κ) (hK : IsSSK G s r c) :
    Ssum (co (subGame G s r c - v • onesMat (Fin s) (Fin s))) ≠ 0 ∧
    ((subGame G s r c - v • onesMat (Fin s) (Fin s)).det = 0 ∧
      IsMatVal (subGame G s r c - v • onesMat (Fin s) (Fin s)) 0 ∧
      IsMatVal (G - v • onesMat ι κ) 0) ∧
    (LinearMap.ker (subGame G s r c - v • onesMat (Fin s) (Fin s)).mulVecLin =
        ℝ ∙ ssCol G s r c ∧
      LinearMap.ker (subGame G s r c - v • onesMat (Fin s) (Fin s))ᵀ.mulVecLin =
        ℝ ∙ ssRow G s r c) ∧
    co (subGame G s r c - v • onesMat (Fin s) (Fin s)) =
      Ssum (co (subGame G s r c - v • onesMat (Fin s) (Fin s))) •
        vecMulVec (ssRow G s r c) (ssCol G s r c) := by
  obtain ⟨hxS, hyS, hNy, hxN⟩ := SSKAux.ssk_facts G v hv s r c hK
  set N := subGame G s r c - v • onesMat (Fin s) (Fin s) with hN
  have hNeq : N = subGame G s r c + (-v) • onesMat (Fin s) (Fin s) := by
    rw [hN, neg_smul, sub_eq_add_neg]
  have hS : Ssum (co N) ≠ 0 := by
    rw [hNeq, (SSKAux.B1_full _).2.1]; exact hK.1
  have hy0 : ssCol G s r c ≠ 0 := by
    intro h0; have := hyS.2; rw [h0] at this; simp at this
  have hx0 : ssRow G s r c ≠ 0 := by
    intro h0; have := hxS.2; rw [h0] at this; simp at this
  have hdet : N.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hy0, hNy⟩
  have hadj : N.adjugate ≠ 0 := by
    intro h0; apply hS; simp [Ssum, co, h0]
  have hadjT : Nᵀ.adjugate ≠ 0 := by
    rw [← adjugate_transpose]; intro h0; apply hadj
    rw [← transpose_transpose N.adjugate, h0, transpose_zero]
  have hxN' : Nᵀ *ᵥ ssRow G s r c = 0 := by rw [mulVec_transpose]; exact hxN
  obtain ⟨hker, hrank⟩ := SSKAux.ker_eq_span N hadj _ hy0 hNy
  obtain ⟨hkerT, _⟩ := SSKAux.ker_eq_span Nᵀ hadjT _ hx0 hxN'
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; exact absurd (Subsingleton.elim (ssCol G 0 r c) 0) hy0
    · exact h
  refine ⟨hS, ⟨hdet, ⟨_, hxS, _, hyS, fun j => ?_, fun i => ?_⟩, ?_⟩, ⟨hker, hkerT⟩, ?_⟩
  · exact le_of_eq (congrFun hxN j).symm
  · exact le_of_eq (congrFun hNy i)
  · have := SSKAux.isMatVal_shift G v (-v) hv
    rwa [add_neg_cancel, neg_smul, ← sub_eq_add_neg] at this
  · obtain ⟨α, hα, hco⟩ := SSKAux.B3_core hs N hrank _ _ hkerT hker
    have hSα : Ssum (co N) = α := by
      rw [hco]
      simp only [Ssum, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
      have : ∑ i, ∑ j, α * (ssRow G s r c i * ssCol G s r c j) =
          α * ((∑ i, ssRow G s r c i) * ∑ j, ssCol G s r c j) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
      rw [this, hxS.2, hyS.2]; ring
    rw [hSα, hco]
