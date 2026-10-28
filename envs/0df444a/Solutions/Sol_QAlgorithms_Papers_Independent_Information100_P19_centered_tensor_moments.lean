-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.centered_tensor_moments
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:36:46.354752+00:00
-- url     : https://prove2.me/submissions/b1dd207c-e3df-4792-945a-a1099732b8fc

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

open scoped BigOperators Matrix ComplexOrder

namespace CTM
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


end CTM

namespace CTM
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


theorem rtm_main {a b : ℕ} (m : ℕ) (hm : 1 ≤ m) (X : Bip a b) (hX : X.IsHermitian) :
    ((rMoment X m : ℝ) : ℂ) = T X (alpha' m) (beta' m) := by
  have hM : (realign X * (realign X)ᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self _
  have htr := trace_pow_herm hM m
  have hr : rMoment X m = ∑ i, hM.eigenvalues i ^ m := by
    rw [rMoment, powerTrace, htr, Complex.ofReal_re]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hc : IsConj (finRotate (m'+1)) (finRotate (m'+1))⁻¹ :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr (Equiv.Perm.cycleType_inv _).symm
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  rw [T_main X hX, show (finRotate (m'+1)).symm = (finRotate (m'+1))⁻¹ from rfl, ← hc, F_conj,
    F_finRotate, htr, hr]

def gS {ι : Type*} [DecidableEq ι] (S : Finset ι) : Equiv.Perm (ι ⊕ ι) where
  toFun x := match x with
    | Sum.inl r => if r ∈ S then Sum.inl r else Sum.inr r
    | Sum.inr r => if r ∈ S then Sum.inr r else Sum.inl r
  invFun x := match x with
    | Sum.inl r => if r ∈ S then Sum.inl r else Sum.inr r
    | Sum.inr r => if r ∈ S then Sum.inr r else Sum.inl r
  left_inv x := by rcases x with r | r <;> by_cases h : r ∈ S <;> simp [h]
  right_inv x := by rcases x with r | r <;> by_cases h : r ∈ S <;> simp [h]

def sig {ι : Type*} (p : Equiv.Perm ι) : Equiv.Perm (ι ⊕ ι) := Equiv.sumCongr p (Equiv.refl ι)

def tau {ι : Type*} [DecidableEq ι] (q : Equiv.Perm ι) (S : Finset ι) : Equiv.Perm (ι ⊕ ι) :=
  (gS S).trans ((Equiv.sumCongr q (Equiv.refl ι)).trans (gS S).symm)

theorem prod_sum2 {ι A B : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (H : ι → A → B → ℂ) :
    ∑ u : ι → A, ∑ v : ι → B, ∏ r, H r (u r) (v r) = ∏ r, ∑ x, ∑ y, H r x y := by
  simp_rw [← Fintype.sum_prod_type']
  rw [Fintype.prod_sum (fun r (z : A × B) => H r z.1 z.2)]
  rw [← (Equiv.arrowProdEquivProdArrow ι (fun _ => A) (fun _ => B)).symm.sum_comp]
  rfl

theorem T_key {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ℕ} (X : Bip a b)
    (p q : Equiv.Perm ι) (S : Finset ι) :
    T X (sig p) (tau q S) = ∑ i : ι → Fin a, ∑ j : ι → Fin b, ∏ r,
      (if r ∈ S then X.trace * X (i r, j r) (i (p r), j (q r))
        else marginalA X (i r) (i (p r)) * marginalB X (j r) (j (q r))) := by
  let H : (ι → Fin a) → (ι → Fin b) → ι → Fin a → Fin b → ℂ := fun i j r x y =>
    if r ∈ S then X (i r, j r) (i (p r), j (q r)) * X (x, y) (x, y)
    else X (i r, y) (i (p r), y) * X (x, j r) (x, j (q r))
  calc T X (sig p) (tau q S)
      = ∑ i : ι → Fin a, ∑ u : ι → Fin a, ∑ j : ι → Fin b, ∑ v : ι → Fin b,
          ∏ r, H i j r (u r) (v r) := by
        unfold T
        rw [← (Equiv.sumArrowEquivProdArrow ι ι (Fin a)).symm.sum_comp, Fintype.sum_prod_type]
        refine Fintype.sum_congr _ _ fun i => Fintype.sum_congr _ _ fun u => ?_
        rw [← (Equiv.arrowCongr (gS S).symm (Equiv.refl (Fin b))).sum_comp,
          ← (Equiv.sumArrowEquivProdArrow ι ι (Fin b)).symm.sum_comp, Fintype.sum_prod_type]
        refine Fintype.sum_congr _ _ fun j => Fintype.sum_congr _ _ fun v => ?_
        rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
        refine Fintype.prod_congr _ _ fun r => ?_
        by_cases h : r ∈ S <;> by_cases h2 : q r ∈ S <;>
          simp [h, h2, H, gS, sig, tau, Equiv.arrowCongr_apply] <;> ring
    _ = ∑ i : ι → Fin a, ∑ j : ι → Fin b, ∑ u : ι → Fin a, ∑ v : ι → Fin b,
          ∏ r, H i j r (u r) (v r) :=
        Fintype.sum_congr _ _ fun i => Finset.sum_comm
    _ = ∑ i : ι → Fin a, ∑ j : ι → Fin b, ∏ r, ∑ x, ∑ y, H i j r x y :=
        Fintype.sum_congr _ _ fun i => Fintype.sum_congr _ _ fun j => prod_sum2 _
    _ = _ := by
        refine Fintype.sum_congr _ _ fun i => Fintype.sum_congr _ _ fun j => ?_
        refine Fintype.prod_congr _ _ fun r => ?_
        by_cases h : r ∈ S
        · simp only [H, h, if_true, ← Finset.mul_sum]
          rw [mul_comm, Matrix.trace, Fintype.sum_prod_type]
          rfl
        · simp only [H, h, if_false, marginalA, marginalB]
          rw [Finset.sum_mul_sum, Finset.sum_comm]

theorem trace_real {a b : ℕ} (X : Bip a b) (hX : X.IsHermitian) :
    ((X.trace.re : ℝ) : ℂ) = X.trace := by
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im, Matrix.trace, Complex.im_sum]
    exact (Finset.sum_eq_zero fun c _ => Complex.conj_eq_iff_im.mp (hX.apply c c)).symm

theorem mass_eq {a b : ℕ} (X : Bip a b) (hX : X.IsHermitian) : ((mass X : ℝ) : ℂ) = X.trace := by
  rw [mass, powerTrace, pow_one, trace_real X hX]

theorem centered_herm {a b : ℕ} (X : Bip a b) (hX : X.IsHermitian) : (centered X).IsHermitian := by
  have hA : ∀ i j, star (marginalA X j i) = marginalA X i j := by
    intro i j; simp [marginalA, star_sum, hX.apply]
  have hB : ∀ i j, star (marginalB X j i) = marginalB X i j := by
    intro i j; simp [marginalB, star_sum, hX.apply]
  ext p q
  simp only [centered, Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.kroneckerMap_apply, Matrix.kronecker, star_sub, smul_eq_mul, star_mul', hA, hB,
    hX.apply, Complex.star_def, Complex.conj_ofReal]

theorem T_centered {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ℕ} (X : Bip a b)
    (hX : X.IsHermitian) (p q : Equiv.Perm ι) :
    T (centered X) p q = ∑ S : Finset ι, (-1 : ℂ) ^ Sᶜ.card * T X (sig p) (tau q S) := by
  have entry : ∀ x y, centered X x y =
      X.trace * X x y + -(marginalA X x.1 y.1 * marginalB X x.2 y.2) := by
    intro x y
    simp [centered, mass_eq X hX, Matrix.kronecker_apply, sub_eq_add_neg]
  simp_rw [T_key, Finset.mul_sum]
  unfold T
  simp_rw [entry, Fintype.prod_add]
  conv_rhs => rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun i => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun j => Fintype.sum_congr _ _ fun S => ?_
  rw [Finset.prod_ite, Finset.prod_neg]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have : (Finset.univ.filter fun x => x ∉ S) = Sᶜ := by ext; simp
  rw [this]
  ring

theorem gen_part (m : ℕ) (hm : 1 ≤ m) : ∃ f : TensorCoeff (4*m), ∀ a b, 0<a → 0<b →
    ∀ X : Bip a b, X.IsHermitian → rMoment (centered X) m = tensorEval f X := by
  have hcard : Fintype.card ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) = 4*m := by simp; ring
  let E := Fintype.equivFinOfCardEq hcard
  refine ⟨fun P => ∑ S : Finset (Fin m ⊕ Fin m),
    if P = (E.permCongr (sig (alpha' m)), E.permCongr (tau (beta' m) S))
    then (-1:ℝ)^Sᶜ.card else 0, fun a b _ _ X hX => ?_⟩
  have h1 := rtm_main m hm (centered X) (centered_herm X hX)
  rw [T_centered X hX] at h1
  have h2 : rMoment (centered X) m =
      (∑ S, (-1:ℂ)^Sᶜ.card * T X (sig (alpha' m)) (tau (beta' m) S)).re := by
    rw [← h1, Complex.ofReal_re]
  rw [h2, Complex.re_sum]
  unfold tensorEval
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun S => ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [show tensorTrace (E.permCongr (sig (alpha' m)), E.permCongr (tau (beta' m) S)) X =
    T X (E.permCongr (sig (alpha' m))) (E.permCongr (tau (beta' m) S)) from rfl, T_permCongr]
  rw [show ((-1:ℂ)^Sᶜ.card) = (((-1:ℝ)^Sᶜ.card : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul]

theorem svals : s34 0 = 0 ∧ s34 1 = 1 ∧ s34 2 = 3 ∧ s34 3 = 2 ∧
    s23 0 = 0 ∧ s23 1 = 2 ∧ s23 2 = 1 ∧ s23 3 = 3 ∧
    s12 0 = 1 ∧ s12 1 = 0 ∧ s12 2 = 2 ∧ s12 3 = 3 := by decide

theorem TT1 {a b : ℕ} (X : Bip a b) :
    tensorTrace (s34, s34) X = X.trace * X.trace * ∑ p : Fin a × Fin b, ∑ q : Fin a × Fin b, X p q * X q p := by
  obtain ⟨c0, c1, c2, c3, -⟩ := svals
  simp only [Matrix.trace, Matrix.diag, marginalA, marginalB, Finset.sum_mul, Finset.mul_sum]
  simp only [← Fintype.sum_prod_type']
  unfold tensorTrace
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_bijective
    (fun ij : (Fin 4 → Fin a) × (Fin 4 → Fin b) => ((ij.1 2, ij.2 2), (ij.1 3, ij.2 3), (ij.1 1, ij.2 1), (ij.1 0, ij.2 0)))
    (Function.bijective_iff_has_inverse.mpr ⟨fun x => (![x.2.2.2.1, x.2.2.1.1, x.1.1, x.2.1.1], ![x.2.2.2.2, x.2.2.1.2, x.1.2, x.2.1.2]),
      fun ij => by
        rcases ij with ⟨i, j⟩
        refine Prod.ext ?_ ?_ <;> (ext r; fin_cases r <;> rfl), fun q => rfl⟩) _ _ (fun ij => ?_)
  rcases ij with ⟨i, j⟩
  simp only [Fin.prod_univ_four, c0, c1, c2, c3]
  ring

theorem TT2 {a b : ℕ} (X : Bip a b) :
    tensorTrace (s34, s23) X = X.trace * ∑ p : Fin a × Fin b, ∑ q : Fin a × Fin b, X p q *
      (marginalA X q.1 p.1 * marginalB X q.2 p.2) := by
  obtain ⟨c0, c1, c2, c3, d0, d1, d2, d3, -⟩ := svals
  simp only [Matrix.trace, Matrix.diag, marginalA, marginalB, Finset.sum_mul, Finset.mul_sum]
  simp only [← Fintype.sum_prod_type']
  unfold tensorTrace
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_bijective
    (fun ij : (Fin 4 → Fin a) × (Fin 4 → Fin b) => ((ij.1 2, ij.2 2), (ij.1 3, ij.2 1), ij.1 1, ij.2 3, (ij.1 0, ij.2 0)))
    (Function.bijective_iff_has_inverse.mpr ⟨fun x => (![x.2.2.2.2.1, x.2.2.1, x.1.1, x.2.1.1], ![x.2.2.2.2.2, x.2.1.2, x.1.2, x.2.2.2.1]),
      fun ij => by
        rcases ij with ⟨i, j⟩
        refine Prod.ext ?_ ?_ <;> (ext r; fin_cases r <;> rfl), fun q => rfl⟩) _ _ (fun ij => ?_)
  rcases ij with ⟨i, j⟩
  simp only [Fin.prod_univ_four, c0, c1, c2, c3, d0, d1, d2, d3]
  ring

theorem TT3 {a b : ℕ} (X : Bip a b) :
    tensorTrace (s12, s34) X = ∑ p : Fin a × Fin b, ∑ q : Fin a × Fin b,
      (marginalA X p.1 q.1 * marginalB X p.2 q.2) * (marginalA X q.1 p.1 * marginalB X q.2 p.2) := by
  obtain ⟨c0, c1, c2, c3, -, -, -, -, e0, e1, e2, e3⟩ := svals
  simp only [Matrix.trace, Matrix.diag, marginalA, marginalB, Finset.sum_mul, Finset.mul_sum]
  simp only [← Fintype.sum_prod_type']
  unfold tensorTrace
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_bijective
    (fun ij : (Fin 4 → Fin a) × (Fin 4 → Fin b) => ((ij.1 0, ij.2 2), (ij.1 1, ij.2 3), ij.1 3, ij.2 1, ij.1 2, ij.2 0))
    (Function.bijective_iff_has_inverse.mpr ⟨fun x => (![x.1.1, x.2.1.1, x.2.2.2.2.1, x.2.2.1], ![x.2.2.2.2.2, x.2.2.2.1, x.1.2, x.2.1.2]),
      fun ij => by
        rcases ij with ⟨i, j⟩
        refine Prod.ext ?_ ?_ <;> (ext r; fin_cases r <;> rfl), fun q => rfl⟩) _ _ (fun ij => ?_)
  rcases ij with ⟨i, j⟩
  simp only [Fin.prod_univ_four, c0, c1, c2, c3, e0, e1, e2, e3]
  ring

theorem rm1 {a b : ℕ} (Y : Bip a b) (hY : Y.IsHermitian) :
    rMoment Y 1 = (∑ p : Fin a × Fin b, ∑ q : Fin a × Fin b, Y p q * Y q p).re := by
  rw [rMoment, powerTrace, pow_one]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, realign,
    hY.apply, Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun u1 => ?_
  rw [Finset.sum_comm]

theorem expand1 {a b : ℕ} (X : Bip a b) (hX : X.IsHermitian) :
    ∑ p : Fin a × Fin b, ∑ q : Fin a × Fin b, centered X p q * centered X q p =
      X.trace * X.trace * (∑ p : Fin a × Fin b, ∑ q : Fin a × Fin b, X p q * X q p) -
      2 * (X.trace * ∑ p : Fin a × Fin b, ∑ q : Fin a × Fin b, X p q *
        (marginalA X q.1 p.1 * marginalB X q.2 p.2)) +
      ∑ p : Fin a × Fin b, ∑ q : Fin a × Fin b,
        (marginalA X p.1 q.1 * marginalB X p.2 q.2) * (marginalA X q.1 p.1 * marginalB X q.2 p.2) := by
  have entry : ∀ x y, centered X x y =
      X.trace * X x y - marginalA X x.1 y.1 * marginalB X x.2 y.2 := by
    intro x y
    simp [centered, mass_eq X hX, Matrix.kronecker_apply]
  have hsym : ∑ p : Fin a × Fin b, ∑ q : Fin a × Fin b,
      (marginalA X p.1 q.1 * marginalB X p.2 q.2) * X q p =
      ∑ p : Fin a × Fin b, ∑ q : Fin a × Fin b, X p q *
        (marginalA X q.1 p.1 * marginalB X q.2 p.2) := by
    rw [Finset.sum_comm]
    exact Fintype.sum_congr _ _ fun p => Fintype.sum_congr _ _ fun q => mul_comm _ _
  simp only [entry]
  have : ∀ p q : Fin a × Fin b,
      (X.trace * X p q - marginalA X p.1 q.1 * marginalB X p.2 q.2) *
        (X.trace * X q p - marginalA X q.1 p.1 * marginalB X q.2 p.2) =
      X.trace * X.trace * (X p q * X q p) -
        X.trace * (X p q * (marginalA X q.1 p.1 * marginalB X q.2 p.2)) -
        X.trace * ((marginalA X p.1 q.1 * marginalB X p.2 q.2) * X q p) +
        (marginalA X p.1 q.1 * marginalB X p.2 q.2) * (marginalA X q.1 p.1 * marginalB X q.2 p.2) := by
    intro p q; ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsym]
  ring

end CTM

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution (m : ℕ) (hm : 1 ≤ m) :
    (∃ f : TensorCoeff (4*m), ∀ a b, 0<a → 0<b → ∀ X : Bip a b,
      X.IsHermitian → rMoment (centered X) m = tensorEval f X) ∧
    (∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.IsHermitian →
      rMoment (centered X) 1 = (tensorTrace (s34,s34) X).re -
        2*(tensorTrace (s34,s23) X).re + (tensorTrace (s12,s34) X).re) := by
  refine ⟨CTM.gen_part m hm, fun a b _ _ X hX => ?_⟩
  rw [CTM.rm1 _ (CTM.centered_herm X hX), CTM.expand1 X hX, CTM.TT1, CTM.TT2, CTM.TT3,
    Complex.add_re, Complex.sub_re]
  rw [show (2:ℂ) * (X.trace * ∑ p : Fin a × Fin b, ∑ q : Fin a × Fin b, X p q *
        (marginalA X q.1 p.1 * marginalB X q.2 p.2)) =
      ((2:ℝ):ℂ) * (X.trace * ∑ p : Fin a × Fin b, ∑ q : Fin a × Fin b, X p q *
        (marginalA X q.1 p.1 * marginalB X q.2 p.2)) by norm_num, Complex.re_ofReal_mul]

