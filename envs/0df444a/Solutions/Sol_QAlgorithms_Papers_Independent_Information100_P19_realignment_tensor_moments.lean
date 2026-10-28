-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.realignment_tensor_moments
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:21:58.417754+00:00
-- url     : https://prove2.me/submissions/f211c916-b3aa-4917-a5a1-a7e33cb21317

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

open scoped BigOperators Matrix ComplexOrder

namespace RTM
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {M : Type*} [Fintype M] [DecidableEq M]

def F {α : Type*} [Fintype α] [DecidableEq α] (Y : Matrix M M ℂ) (σ : Equiv.Perm α) : ℂ :=
  ∑ κ : α → M, ∏ r, Y (κ r) (κ (σ r))

theorem F_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (Y : Matrix M M ℂ) (e : α ≃ β) (σ : Equiv.Perm α) : F Y (e.permCongr σ) = F Y σ := by
  unfold F
  rw [← (e.arrowCongr (Equiv.refl M)).sum_comp]
  refine Fintype.sum_congr _ _ fun κ => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id,
    Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact e.symm.prod_comp (fun r => Y (κ r) (κ (σ r)))

theorem F_conj {α : Type*} [Fintype α] [DecidableEq α] (Y : Matrix M M ℂ) (c σ : Equiv.Perm α) :
    F Y (c * σ * c⁻¹) = F Y σ := by
  have : c * σ * c⁻¹ = c.permCongr σ := by
    ext x; simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply]
  rw [this, F_permCongr]

theorem F_sumCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (Y : Matrix M M ℂ) (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    F Y (Equiv.Perm.sumCongr σ τ) = F Y σ * F Y τ := by
  unfold F
  rw [← (Equiv.sumArrowEquivProdArrow α β M).symm.sum_comp, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  refine Fintype.sum_congr _ _ fun u => Fintype.sum_congr _ _ fun v => ?_
  simp [Fintype.prod_sum_type]

theorem pow_path (Y : Matrix M M ℂ) : ∀ (m : ℕ) (a b : M), (Y ^ (m + 1)) a b =
    ∑ κ : Fin m → M, ∏ r : Fin (m + 1),
      Y ((Fin.cons a κ : Fin (m + 1) → M) r) ((Fin.snoc κ b : Fin (m + 1) → M) r)
  | 0, a, b => by
    simp [Fin.snoc]
  | m + 1, a, b => by
    rw [pow_succ', Matrix.mul_apply]
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => M).sum_comp, Fintype.sum_prod_type]
    refine Fintype.sum_congr _ _ fun c => ?_
    rw [pow_path Y m c b, Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun κ => ?_
    rw [Fin.prod_univ_succ (n := m + 1)]
    change Y a c * _ = Y a ((Fin.snoc (Fin.cons c κ : Fin (m+1) → M) b : Fin (m+2) → M) 0) *
      ∏ x : Fin (m+1), Y ((Fin.cons c κ : Fin (m+1) → M) x)
        ((Fin.snoc (Fin.cons c κ : Fin (m+1) → M) b : Fin (m+2) → M) x.succ)
    rw [← Fin.cons_snoc_eq_snoc_cons]
    simp only [Fin.cons_zero, Fin.cons_succ]

theorem F_finRotate (Y : Matrix M M ℂ) (m : ℕ) : F Y (finRotate (m + 1)) = (Y ^ (m + 1)).trace := by
  unfold F
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, pow_path Y m]
  rw [← (Fin.consEquiv fun _ : Fin (m + 1) => M).sum_comp, Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun a => Fintype.sum_congr _ _ fun κ => ?_
  refine Fintype.prod_congr _ _ fun r => ?_
  simp only [Fin.consEquiv_apply]
  congr 1
  induction r using Fin.lastCases with
  | last => simp [finRotate_last]
  | cast i =>
    rw [Fin.snoc_castSucc, finRotate_apply]
    have : (Fin.castSucc i + 1 : Fin (m + 1)) = i.succ := by
      ext; simp [Fin.val_add, Nat.mod_eq_of_lt (Nat.succ_lt_succ i.isLt)]
    rw [this, Fin.cons_succ]


end RTM

namespace RTM
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open QAlgorithms.Papers.Independent.Information100.P19

theorem trace_pow_herm {I : Type*} [Fintype I] [DecidableEq I] {Y : Matrix I I ℂ}
    (hY : Y.IsHermitian) (k : ℕ) :
    (Y ^ k).trace = ((∑ i, hY.eigenvalues i ^ k : ℝ) : ℂ) := by
  have hs := hY.spectral_theorem
  have : Y ^ k = Unitary.conjStarAlgAut ℂ _ hY.eigenvectorUnitary
      ((Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues)) ^ k) := by
    rw [map_pow, ← hs]
  rw [this, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm, ← mul_assoc,
    Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  push_cast
  rfl

theorem fp2 {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup) (p q : α) (hpq : p ≠ q)
    (hm : ∀ x, x ∈ l ↔ x = p ∨ x = q) : l.formPerm = Equiv.swap p q := by
  have hlen : l.length = 2 := by
    rw [← List.toFinset_card_of_nodup hl]
    have : l.toFinset = {p, q} := by ext x; simp [hm]
    rw [this, Finset.card_pair hpq]
  match l, hl, hm, hlen with
  | [x, y], hl, hm, _ =>
    rw [List.formPerm_pair]
    have hxy : x ≠ y := by simpa using hl
    have hx := (hm x).1 (by simp)
    have hy := (hm y).1 (by simp)
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · rfl
    · exact Equiv.swap_comm _ _
    · exact absurd rfl hxy

theorem swap_val {n : ℕ} (p q y : Fin n) : (Equiv.swap p q y).val =
    if y.val = p.val then q.val else if y.val = q.val then p.val else y.val := by
  rw [Equiv.swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff]

theorem pairProd {n c : ℕ} (L : ℕ → List (Fin n))
    (hL : ∀ j, (L j).Nodup ∧ ∀ x : Fin n, x ∈ L j ↔ (x.val = 2*j+c ∨ x.val = 2*j+c+1)) :
    ∀ k, 2*k+c ≤ n → ∀ x : Fin n, (((List.range k).map fun j => (L j).formPerm).prod x).val =
      if c ≤ x.val ∧ x.val < 2*k+c then (if (x.val - c) % 2 = 0 then x.val+1 else x.val-1)
      else x.val
  | 0, _, x => by simp
  | k + 1, hk, x => by
    have ih := pairProd L hL k (by omega)
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, Equiv.Perm.mul_apply,
      fp2 (L k) (hL k).1 ⟨2*k+c, by omega⟩ ⟨2*k+c+1, by omega⟩ (by simp)
        (fun x => by rw [(hL k).2, Fin.ext_iff, Fin.ext_iff])]
    rw [ih, swap_val]
    simp only
    split_ifs <;> omega

theorem beta_val (m : ℕ) (x : Fin (2*m)) :
    (betaPerm m x).val = if x.val % 2 = 0 then x.val + 1 else x.val - 1 := by
  unfold betaPerm
  rw [pairProd (c := 0) _ (fun j => ⟨(List.nodup_finRange _).filter _, fun x => by simp⟩) m
    (by omega) x]
  split_ifs <;> omega

theorem alpha_val (m : ℕ) (hm : 1 ≤ m) (x : Fin (2*m)) :
    (alphaPerm m x).val = if x.val = 0 then 2*m-1 else if x.val = 2*m-1 then 0 else
      if x.val % 2 = 1 then x.val + 1 else x.val - 1 := by
  unfold alphaPerm
  rw [Equiv.Perm.mul_apply, fp2 _ ((List.nodup_finRange _).filter _) ⟨0, by omega⟩
    ⟨2*m-1, by omega⟩ (by simp [Fin.ext_iff]; omega)
    (fun x => by simp [Fin.ext_iff]; omega)]
  have h := pairProd (c := 1) _ (fun j => ⟨(List.nodup_finRange (2*m)).filter
    (fun i => decide (i.val = 2*j+1 ∨ i.val = 2*j+2)), fun x => by simp⟩) (m-1) (by omega) x
  have hx := x.isLt
  split_ifs at h <;> rw [swap_val, h] <;> simp only <;> split_ifs <;> first | omega | contradiction


noncomputable def e (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2*m) :=
  Equiv.ofBijective (Sum.elim (fun t => ⟨2*t.val, by omega⟩) (fun t => ⟨2*t.val+1, by omega⟩)) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp; ring⟩
    intro x y h
    rcases x with x | x <;> rcases y with y | y <;> simp [Fin.ext_iff] at h ⊢ <;> omega)

def alpha' (m : ℕ) : Equiv.Perm (Fin m ⊕ Fin m) :=
  (Equiv.sumCongr (finRotate m).symm (finRotate m)).trans (Equiv.sumComm _ _)

def beta' (m : ℕ) : Equiv.Perm (Fin m ⊕ Fin m) := Equiv.sumComm _ _

theorem beta_eq (m : ℕ) : betaPerm m = (e m).permCongr (beta' m) := by
  refine Equiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (e m).surjective y
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  apply Fin.ext
  rw [beta_val]
  rcases x with t | t <;> simp [beta', e] <;> omega

theorem alpha_eq (m : ℕ) (hm : 1 ≤ m) : alphaPerm m = (e m).permCongr (alpha' m) := by
  refine Equiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (e m).surjective y
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  apply Fin.ext
  rw [alpha_val m hm]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hrot : ∀ t : Fin (m'+1), ((finRotate (m'+1)) t).val = if t.val = m' then 0 else t.val + 1 := by
    intro t
    rw [coe_finRotate]
    simp [Fin.ext_iff]
  rcases x with s | t
  · obtain ⟨t, rfl⟩ := (finRotate _).surjective s
    simp only [alpha', e, Equiv.ofBijective_apply, Sum.elim_inl, Sum.elim_inr,
      Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumComm_apply, Sum.swap_inl,
      Equiv.symm_apply_apply]
    have ht := t.isLt
    have h := hrot t
    split_ifs at h <;> rw [h] <;> split_ifs <;> first | omega | contradiction
  · simp only [alpha', e, Equiv.ofBijective_apply, Sum.elim_inl, Sum.elim_inr,
      Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumComm_apply, Sum.swap_inr]
    have ht := t.isLt
    have h := hrot t
    split_ifs at h <;> rw [h] <;> split_ifs <;> first | omega | contradiction

def T {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ℕ} (X : Bip a b) (p q : Equiv.Perm ι) : ℂ :=
  ∑ i : ι → Fin a, ∑ j : ι → Fin b, ∏ r, X (i r, j r) (i (p r), j (q r))

theorem T_permCongr {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {a b : ℕ} (X : Bip a b) (e : ι ≃ κ) (p q : Equiv.Perm ι) :
    T X (e.permCongr p) (e.permCongr q) = T X p q := by
  unfold T
  rw [← (e.arrowCongr (Equiv.refl (Fin a))).sum_comp]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [← (e.arrowCongr (Equiv.refl (Fin b))).sum_comp]
  refine Fintype.sum_congr _ _ fun j => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id,
    Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact e.symm.prod_comp (fun r => X (i r, j r) (i (p r), j (q r)))

theorem T_main {a b : ℕ} (X : Bip a b) (hX : X.IsHermitian) (m : ℕ) :
    T X (alpha' m) (beta' m) = F (realign X * (realign X)ᴴ) (finRotate m).symm := by
  set R := realign X with hR
  set rot := finRotate m with hrot
  calc T X (alpha' m) (beta' m)
      = ∑ iL : Fin m → Fin a, ∑ iR : Fin m → Fin a, ∑ jL : Fin m → Fin b, ∑ jR : Fin m → Fin b,
          (∏ t, X (iL t, jL t) (iR (rot.symm t), jR t)) *
            ∏ t, X (iR t, jR t) (iL (rot t), jL t) := by
        unfold T
        rw [← (Equiv.sumArrowEquivProdArrow (Fin m) (Fin m) (Fin a)).symm.sum_comp,
          Fintype.sum_prod_type]
        refine Fintype.sum_congr _ _ fun iL => Fintype.sum_congr _ _ fun iR => ?_
        rw [← (Equiv.sumArrowEquivProdArrow (Fin m) (Fin m) (Fin b)).symm.sum_comp,
          Fintype.sum_prod_type]
        refine Fintype.sum_congr _ _ fun jL => Fintype.sum_congr _ _ fun jR => ?_
        simp [Fintype.prod_sum_type, alpha', beta', rot]
    _ = ∑ iR : Fin m → Fin a, ∑ iL : Fin m → Fin a, ∑ jR : Fin m → Fin b, ∑ jL : Fin m → Fin b,
          ∏ t, R (iR t, iL (rot t)) (jR t, jL t) *
            star (R (iR (rot.symm t), iL t) (jR t, jL t)) := by
        rw [Finset.sum_comm]
        refine Fintype.sum_congr _ _ fun iR => Fintype.sum_congr _ _ fun iL => ?_
        rw [Finset.sum_comm]
        refine Fintype.sum_congr _ _ fun jR => Fintype.sum_congr _ _ fun jL => ?_
        rw [Finset.prod_mul_distrib, mul_comm]
        congr 1
        refine Fintype.prod_congr _ _ fun t => ?_
        simp only [hR, realign]
        exact (hX.apply _ _).symm
    _ = ∑ u1 : Fin m → Fin a, ∑ u2 : Fin m → Fin a, ∑ v1 : Fin m → Fin b, ∑ v2 : Fin m → Fin b,
          ∏ t, R (u1 t, u2 t) (v1 t, v2 t) *
            star (R (u1 (rot.symm t), u2 (rot.symm t)) (v1 t, v2 t)) := by
        refine Fintype.sum_congr _ _ fun iR => ?_
        conv_rhs => rw [← (Equiv.arrowCongr rot.symm (Equiv.refl (Fin a))).sum_comp]
        refine Fintype.sum_congr _ _ fun iL => ?_
        simp [Equiv.arrowCongr_apply]
    _ = ∑ U : Fin m → (Fin a × Fin a), ∑ V : Fin m → (Fin b × Fin b),
          ∏ t, R (U t) (V t) * star (R (U (rot.symm t)) (V t)) := by
        rw [← (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => Fin a) (fun _ => Fin a)).symm.sum_comp,
          Fintype.sum_prod_type]
        refine Fintype.sum_congr _ _ fun u1 => Fintype.sum_congr _ _ fun u2 => ?_
        rw [← (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => Fin b) (fun _ => Fin b)).symm.sum_comp,
          Fintype.sum_prod_type]
        rfl
    _ = F (R * Rᴴ) rot.symm := by
        unfold F
        refine Fintype.sum_congr _ _ fun U => ?_
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
        exact (Fintype.prod_sum (fun t v => R (U t) v * star (R (U (rot.symm t)) v))).symm

end RTM

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution (m : ℕ) (hm : 1 ≤ m) (a b : ℕ) (ha : 0<a) (hb : 0<b)
    (X : Bip a b) (hX : X.IsHermitian) :
    rMoment X m = ((singularSpectrum (realign X)).map (fun s => s^(2*m))).sum ∧
    ((rMoment X m : ℝ) : ℂ) = tensorTrace (alphaPerm m,betaPerm m) X := by
  have hM : (realign X * (realign X)ᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self _
  have hP : (realign X * (realign X)ᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose _
  have htr := RTM.trace_pow_herm hM m
  have hr : rMoment X m = ∑ i, hM.eigenvalues i ^ m := by
    rw [rMoment, powerTrace, htr, Complex.ofReal_re]
  constructor
  · rw [hr, singularSpectrum, eigenSpectrum, hM.roots_charpoly_eq_eigenvalues]
    simp only [Multiset.map_map, Function.comp_def]
    rw [Finset.sum_map_val]
    refine Fintype.sum_congr _ _ fun i => ?_
    change hM.eigenvalues i ^ m = Real.sqrt (hM.eigenvalues i) ^ (2*m)
    rw [pow_mul, Real.sq_sqrt (hP.eigenvalues_nonneg i)]
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h1 : tensorTrace (alphaPerm (m'+1), betaPerm (m'+1)) X =
        RTM.T X (alphaPerm (m'+1)) (betaPerm (m'+1)) := rfl
    have hc : IsConj (finRotate (m'+1)) (finRotate (m'+1))⁻¹ :=
      Equiv.Perm.isConj_iff_cycleType_eq.mpr (Equiv.Perm.cycleType_inv _).symm
    obtain ⟨c, hc⟩ := isConj_iff.mp hc
    rw [h1, RTM.alpha_eq _ hm, RTM.beta_eq, RTM.T_permCongr, RTM.T_main X hX,
      show (finRotate (m'+1)).symm = (finRotate (m'+1))⁻¹ from rfl, ← hc, RTM.F_conj,
      RTM.F_finRotate, htr, hr]

