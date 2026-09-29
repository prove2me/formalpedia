-- Prove2me | solution 1 for TSPHeuristics.KOpt.theorem_6_k_optimal_ratio_two_mul_one_sub_inv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:55:40.433359+00:00
-- url     : https://prove2.me/submissions/59dcf8ed-7f6f-443c-b5fe-d171dfb7a9bd

import Mathlib
import Definitions.Def_TSPHeuristics_KOpt_KOptimal

namespace TSPHeuristics.KOpt

open TSPHeuristics.Shared

/-- canonical arc between `x` and `y` on a cycle of `n` nodes; unit edge `e` joins `e` and `e+1`. -/
def aux_ko6_arc (n : ℕ) (x y e : ℕ) : Prop :=
  if 2 * (max x y - min x y) ≤ n then min x y ≤ e ∧ e < max x y
  else e < min x y ∨ max x y ≤ e

instance aux_ko6_arc_dec (n x y e : ℕ) : Decidable (aux_ko6_arc n x y e) := by
  unfold aux_ko6_arc; infer_instance

def aux_ko6_cnt {n : ℕ} (σ : Equiv.Perm (Fin n)) (e : Fin n) : ℕ :=
  (Finset.univ.filter
    (fun j : Fin n => aux_ko6_arc n (σ j).val (σ (finRotate n j)).val e.val)).card

def aux_ko6_dN (n : ℕ) (x y : Fin n) : ℕ :=
  (Finset.univ.filter (fun e : Fin n => aux_ko6_arc n x.val y.val e.val)).card

noncomputable def aux_ko6_d (n : ℕ) (x y : Fin n) : ℝ := (aux_ko6_dN n x y : ℝ)

lemma aux_ko6_fr (n : ℕ) (i : Fin n) :
    (finRotate n i).val = if i.val + 1 = n then 0 else i.val + 1 := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    rw [coe_finRotate]
    by_cases h : i = Fin.last m
    · subst h; simp
    · have : i.val ≠ m := fun h' => h (Fin.ext (by simp [h']))
      rw [if_neg h, if_neg (by omega)]

lemma aux_ko6_fr_ne (n : ℕ) (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  intro h
  have := congrArg Fin.val h
  rw [aux_ko6_fr] at this
  split_ifs at this <;> omega

lemma aux_ko6_xor (n : ℕ) (x y : ℕ) (hx : x < n) (hy : y < n) (hxy : x ≠ y) (e : ℕ)
    (_he : e < n) (e' : ℕ) (he' : e' = if e + 1 = n then 0 else e + 1) :
    ((aux_ko6_arc n x y e ∧ ¬ aux_ko6_arc n x y e') ∨ (aux_ko6_arc n x y e' ∧ ¬ aux_ko6_arc n x y e))
      ↔ (x = e' ∨ y = e') := by
  unfold aux_ko6_arc
  split_ifs at he' ⊢ <;> omega


lemma aux_ko6_card_Ico (n a b : ℕ) (hb : b ≤ n) :
    (Finset.univ.filter (fun e : Fin n => a ≤ e.val ∧ e.val < b)).card = b - a := by
  have : (Finset.univ.filter (fun e : Fin n => a ≤ e.val ∧ e.val < b)).map Fin.valEmbedding
      = Finset.Ico a b := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨e, he, rfl⟩; exact he
    · rintro h; exact ⟨⟨x, by omega⟩, h, rfl⟩
  rw [← Finset.card_map, this, Nat.card_Ico]

lemma aux_ko6_dN_eq (n : ℕ) (x y : Fin n) : aux_ko6_dN n x y =
    if 2 * (max x.val y.val - min x.val y.val) ≤ n then max x.val y.val - min x.val y.val
    else n - (max x.val y.val - min x.val y.val) := by
  have hx := x.isLt; have hy := y.isLt
  unfold aux_ko6_dN aux_ko6_arc
  by_cases h : 2 * (max x.val y.val - min x.val y.val) ≤ n
  · simp only [h, if_true]
    exact aux_ko6_card_Ico n _ _ (by omega)
  · simp only [h, if_false]
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun e : Fin n => min x.val y.val ≤ e.val ∧ e.val < max x.val y.val)
    rw [aux_ko6_card_Ico n _ _ (by omega), Finset.card_univ, Fintype.card_fin] at h1
    have h2 : (Finset.univ.filter
        (fun e : Fin n => e.val < min x.val y.val ∨ max x.val y.val ≤ e.val)) =
        Finset.univ.filter
          (fun e : Fin n => ¬ (min x.val y.val ≤ e.val ∧ e.val < max x.val y.val)) := by
      ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    rw [h2]; omega

lemma aux_ko6_arc_comm (n x y e : ℕ) : aux_ko6_arc n x y e ↔ aux_ko6_arc n y x e := by
  unfold aux_ko6_arc; rw [max_comm, min_comm]

lemma aux_ko6_tri (n : ℕ) (x y z : Fin n) :
    aux_ko6_dN n x z ≤ aux_ko6_dN n x y + aux_ko6_dN n y z := by
  rw [aux_ko6_dN_eq, aux_ko6_dN_eq, aux_ko6_dN_eq]
  have := x.isLt; have := y.isLt; have := z.isLt
  split_ifs <;> omega

lemma aux_ko6_isTSP (n : ℕ) : IsTSPDist (aux_ko6_d n) where
  symm i j := by
    unfold aux_ko6_d
    congr 1
    rw [aux_ko6_dN_eq, aux_ko6_dN_eq]
    split_ifs <;> omega
  nonneg i j := by unfold aux_ko6_d; positivity
  triangle i j k := by unfold aux_ko6_d; exact_mod_cast aux_ko6_tri n i j k
  diag i := by unfold aux_ko6_d; rw [aux_ko6_dN_eq]; simp

lemma aux_ko6_sum_swap (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ∑ j, aux_ko6_dN n (σ j) (σ (finRotate n j)) = ∑ e, aux_ko6_cnt σ e := by
  unfold aux_ko6_dN aux_ko6_cnt
  simp only [Finset.card_filter]
  exact Finset.sum_comm

lemma aux_ko6_len (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    tourLength (aux_ko6_d n) σ = ((∑ e, aux_ko6_cnt σ e : ℕ) : ℝ) := by
  unfold tourLength aux_ko6_d
  rw [← aux_ko6_sum_swap, Nat.cast_sum]

lemma aux_ko6_par_step (n : ℕ) (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n)) (e : Fin n) :
    (aux_ko6_cnt σ e + aux_ko6_cnt σ (finRotate n e)) % 2 = 0 := by
  set A := Finset.univ.filter
    (fun j : Fin n => aux_ko6_arc n (σ j).val (σ (finRotate n j)).val e.val) with hA
  set B := Finset.univ.filter
    (fun j : Fin n => aux_ko6_arc n (σ j).val (σ (finRotate n j)).val (finRotate n e).val)
    with hB
  have hA' : aux_ko6_cnt σ e = A.card := rfl
  have hB' : aux_ko6_cnt σ (finRotate n e) = B.card := rfl
  have h1 := Finset.card_sdiff_add_card_inter A B
  have h2 := Finset.card_sdiff_add_card_inter B A
  have hsd : (A \ B) ∪ (B \ A) = Finset.univ.filter
      (fun j => σ j = finRotate n e ∨ σ (finRotate n j) = finRotate n e) := by
    ext j
    simp only [hA, hB, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
      true_and]
    have hne : (σ j).val ≠ (σ (finRotate n j)).val := by
      intro h
      exact aux_ko6_fr_ne n hn j (σ.injective (Fin.ext h)).symm
    have := aux_ko6_xor n _ _ (σ j).isLt (σ (finRotate n j)).isLt hne e.val e.isLt _
      (aux_ko6_fr n e)
    simp only [Fin.ext_iff]
    exact this
  have h3 := Finset.card_union_of_disjoint (disjoint_sdiff_sdiff : Disjoint (A \ B) (B \ A))
  have h4 : (Finset.univ.filter
      (fun j => σ j = finRotate n e ∨ σ (finRotate n j) = finRotate n e)).card = 2 := by
    rw [Finset.card_eq_two]
    refine ⟨σ.symm (finRotate n e), (finRotate n).symm (σ.symm (finRotate n e)), ?_, ?_⟩
    · intro h
      apply aux_ko6_fr_ne n hn (σ.symm (finRotate n e))
      have h' := congrArg (finRotate n) h
      rw [Equiv.apply_symm_apply] at h'
      exact h'
    · ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Equiv.eq_symm_apply]
  rw [hsd, h4] at h3
  have h5 : B ∩ A = A ∩ B := Finset.inter_comm _ _
  rw [h5] at h2
  rw [hA', hB']
  omega

lemma aux_ko6_par0 (n : ℕ) (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n)) (e : Fin n) :
    aux_ko6_cnt σ e % 2 = aux_ko6_cnt σ ⟨0, by omega⟩ % 2 := by
  obtain ⟨t, ht⟩ := e
  induction t with
  | zero => rfl
  | succ t ih =>
    have h := aux_ko6_par_step n hn σ ⟨t, by omega⟩
    have hfr : finRotate n ⟨t, by omega⟩ = ⟨t + 1, ht⟩ := by
      ext; rw [aux_ko6_fr]; simp only; rw [if_neg (by omega)]
    rw [hfr] at h
    have := ih (by omega)
    omega

lemma aux_ko6_par (n : ℕ) (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n)) (e e' : Fin n) :
    aux_ko6_cnt σ e % 2 = aux_ko6_cnt σ e' % 2 := by
  rw [aux_ko6_par0 n hn σ e, aux_ko6_par0 n hn σ e']

lemma aux_ko6_conn (n : ℕ) (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n)) (P : Fin n → Prop)
    (a b : Fin n) (ha : P a) (hb : ¬ P b) :
    ∃ j, P (σ j) ∧ ¬ P (σ (finRotate n j)) := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ t : ℕ, P (σ ((finRotate n ^ t) (σ.symm a))) := by
    intro t
    induction t with
    | zero => simpa using ha
    | succ t ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hcon _ ih
  obtain ⟨t, ht⟩ := (isCycle_finRotate_of_le hn).exists_pow_eq
    (aux_ko6_fr_ne n hn (σ.symm a)) (aux_ko6_fr_ne n hn (σ.symm b))
  apply hb
  have := key t
  rwa [ht, Equiv.apply_symm_apply] at this

lemma aux_ko6_two_zero (n : ℕ) (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n)) (e1 e2 : Fin n)
    (hlt : e1.val < e2.val) (h1 : aux_ko6_cnt σ e1 = 0) (h2 : aux_ko6_cnt σ e2 = 0) : False := by
  unfold aux_ko6_cnt at h1 h2
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1 h2
  obtain ⟨j, hj1, hj2⟩ := aux_ko6_conn n hn σ (fun v => e1.val < v.val ∧ v.val ≤ e2.val) e2 e1
    ⟨hlt, le_refl _⟩ (by simp)
  have c1 := h1 (Finset.mem_univ j)
  have c2 := h2 (Finset.mem_univ j)
  unfold aux_ko6_arc at c1 c2
  have := (σ j).isLt; have := (σ (finRotate n j)).isLt
  split_ifs at c1 c2 <;> omega

lemma aux_ko6_even (n : ℕ) (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n))
    (hev : ∀ e, aux_ko6_cnt σ e % 2 = 0) :
    2 * (n - 1) ≤ ∑ e, aux_ko6_cnt σ e := by
  by_cases hz : ∃ e0, aux_ko6_cnt σ e0 = 0
  · obtain ⟨e0, he0⟩ := hz
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e0)]
    have : ∀ e ∈ Finset.univ.erase e0, 2 ≤ aux_ko6_cnt σ e := by
      intro e he
      have hne : e ≠ e0 := Finset.ne_of_mem_erase he
      have h2 := hev e
      by_contra hlt
      have hz' : aux_ko6_cnt σ e = 0 := by omega
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
      · exact aux_ko6_two_zero n hn σ e e0 h hz' he0
      · exact aux_ko6_two_zero n hn σ e0 e h he0 hz'
    have := (Finset.card_nsmul_le_sum _ _ 2 this :
      (Finset.univ.erase e0).card • 2 ≤ ∑ e ∈ Finset.univ.erase e0, aux_ko6_cnt σ e)
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at this
    omega
  · push_neg at hz
    have : ∀ e ∈ (Finset.univ : Finset (Fin n)), 2 ≤ aux_ko6_cnt σ e := by
      intro e _; have := hev e; have := hz e; omega
    have := (Finset.card_nsmul_le_sum _ _ 2 this :
      (Finset.univ : Finset (Fin n)).card • 2 ≤ ∑ e, aux_ko6_cnt σ e)
    rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    omega

lemma aux_ko6_lower (n : ℕ) (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n)) :
    n ≤ ∑ e, aux_ko6_cnt σ e := by
  by_cases hpar : ∀ e, aux_ko6_cnt σ e % 2 = 0
  · have := aux_ko6_even n hn σ hpar; omega
  · push_neg at hpar
    obtain ⟨e0, he0⟩ := hpar
    have : ∀ e ∈ (Finset.univ : Finset (Fin n)), 1 ≤ aux_ko6_cnt σ e := by
      intro e _; have := aux_ko6_par n hn σ e e0; omega
    have := (Finset.card_nsmul_le_sum _ _ 1 this :
      (Finset.univ : Finset (Fin n)).card • 1 ≤ ∑ e, aux_ko6_cnt σ e)
    rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    omega


lemma aux_ko6_edge_inj (n : ℕ) (hn : 3 ≤ n) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (fun i => s(σ i, σ (finRotate n i))) := by
  intro i j h
  simp only [Sym2.eq_iff] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact σ.injective h1
  · exfalso
    have v1 : i.val = (finRotate n j).val := congrArg Fin.val (σ.injective h1)
    have v2 : (finRotate n i).val = j.val := congrArg Fin.val (σ.injective h2)
    rw [aux_ko6_fr] at v1 v2
    have := i.isLt; have := j.isLt
    split_ifs at v1 v2 <;> omega

lemma aux_ko6_RI_card (n : ℕ) (hn : 3 ≤ n) (τ σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun i => s(τ i, τ (finRotate n i)) ∉ tourEdges σ)).card
      = (tourEdges τ \ tourEdges σ).card := by
  have : tourEdges τ \ tourEdges σ =
      (Finset.univ.filter (fun i => s(τ i, τ (finRotate n i)) ∉ tourEdges σ)).image
        (fun i => s(τ i, τ (finRotate n i))) := by
    ext f
    simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold tourEdges
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, rfl⟩, hf⟩; exact ⟨i, hf, rfl⟩
    · rintro ⟨i, hf, rfl⟩; exact ⟨⟨i, rfl⟩, hf⟩
  rw [this, Finset.card_image_of_injective _ (aux_ko6_edge_inj n hn τ)]

lemma aux_ko6_arc_sym2 {n : ℕ} {a b c d : Fin n} (h : s(a, b) = s(c, d)) (e : ℕ) :
    aux_ko6_arc n a.val b.val e ↔ aux_ko6_arc n c.val d.val e := by
  rw [Sym2.eq_iff] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Iff.rfl
  · exact aux_ko6_arc_comm _ _ _ _

def aux_ko6_J {n : ℕ} (τ σ : Equiv.Perm (Fin n)) (i : Fin n) : Fin n :=
  if σ (finRotate n (σ.symm (τ i))) = τ (finRotate n i) then σ.symm (τ i)
  else σ.symm (τ (finRotate n i))

lemma aux_ko6_J_spec {n : ℕ} (τ σ : Equiv.Perm (Fin n)) (i : Fin n)
    (h : s(τ i, τ (finRotate n i)) ∈ tourEdges σ) :
    s(σ (aux_ko6_J τ σ i), σ (finRotate n (aux_ko6_J τ σ i))) = s(τ i, τ (finRotate n i)) := by
  unfold tourEdges at h
  obtain ⟨j0, _, hj0⟩ := Finset.mem_image.mp h
  unfold aux_ko6_J
  split_ifs with hc
  · rw [Equiv.apply_symm_apply, hc]
  · rw [Sym2.eq_iff] at hj0
    rcases hj0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso; apply hc; rw [← h1, Equiv.symm_apply_apply]; exact h2
    · rw [← h1, Equiv.symm_apply_apply, h2]; exact Sym2.eq_swap

def aux_ko6_tf (n : ℕ) (i : Fin n) : Fin n :=
  ⟨if 2 * i.val < n then 2 * i.val else 2 * (n - 1 - i.val) + 1, by
    have := i.isLt; split_ifs <;> omega⟩

lemma aux_ko6_tf_inj (n : ℕ) : Function.Injective (aux_ko6_tf n) := by
  intro i j h
  have h' := congrArg Fin.val h
  simp only [aux_ko6_tf] at h'
  have := i.isLt; have := j.isLt
  ext; split_ifs at h' <;> omega

noncomputable def aux_ko6_tau (n : ℕ) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (aux_ko6_tf n) (Finite.injective_iff_bijective.mp (aux_ko6_tf_inj n))

lemma aux_ko6_tau_val (n : ℕ) (i : Fin n) : (aux_ko6_tau n i).val =
    if 2 * i.val < n then 2 * i.val else 2 * (n - 1 - i.val) + 1 := rfl

lemma aux_ko6_tau_dN (n : ℕ) (hn : 8 ≤ n) (i : Fin n) :
    aux_ko6_dN n (aux_ko6_tau n i) (aux_ko6_tau n (finRotate n i)) ≤ 2 ∧
    ((i.val = n - 1 ∨ i.val = (n - 1) / 2) →
      aux_ko6_dN n (aux_ko6_tau n i) (aux_ko6_tau n (finRotate n i)) ≤ 1) := by
  rw [aux_ko6_dN_eq, aux_ko6_tau_val, aux_ko6_tau_val, aux_ko6_fr]
  have := i.isLt
  split_ifs <;> omega

lemma aux_ko6_tau_arc (n : ℕ) (hn : 8 ≤ n) (i : Fin n) (e : ℕ)
    (h : aux_ko6_arc n (aux_ko6_tau n i).val (aux_ko6_tau n (finRotate n i)).val e) :
    e < n - 1 := by
  unfold aux_ko6_arc at h
  rw [aux_ko6_tau_val, aux_ko6_tau_val, aux_ko6_fr] at h
  have := i.isLt
  split_ifs at h <;> omega

lemma aux_ko6_tau_zero (n : ℕ) (hn : 8 ≤ n) :
    aux_ko6_cnt (aux_ko6_tau n) ⟨n - 1, by omega⟩ = 0 := by
  unfold aux_ko6_cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _ hj
  have := aux_ko6_tau_arc n hn j _ hj
  simp at this

lemma aux_ko6_tau_even (n : ℕ) (hn : 8 ≤ n) (e : Fin n) :
    aux_ko6_cnt (aux_ko6_tau n) e % 2 = 0 := by
  rw [aux_ko6_par n (by omega) _ e ⟨n - 1, by omega⟩, aux_ko6_tau_zero n hn]

lemma aux_ko6_tau_cnt (n : ℕ) (hn : 8 ≤ n) (e : Fin n) (he : e.val < n - 1) :
    2 ≤ aux_ko6_cnt (aux_ko6_tau n) e := by
  have hp := aux_ko6_tau_even n hn e
  by_contra hlt
  have h0 : aux_ko6_cnt (aux_ko6_tau n) e = 0 := by omega
  exact aux_ko6_two_zero n (by omega) _ e ⟨n - 1, by omega⟩ he h0 (aux_ko6_tau_zero n hn)

lemma aux_ko6_tau_sum (n : ℕ) (hn : 8 ≤ n) :
    ∑ e, aux_ko6_cnt (aux_ko6_tau n) e = 2 * n - 2 := by
  apply le_antisymm
  · rw [← aux_ko6_sum_swap]
    have hScard : (Finset.univ.filter
        (fun i : Fin n => i.val = n - 1 ∨ i.val = (n - 1) / 2)).card = 2 := by
      rw [Finset.card_eq_two]
      refine ⟨⟨n - 1, by omega⟩, ⟨(n - 1) / 2, by omega⟩, ?_, ?_⟩
      · simp only [ne_eq, Fin.mk.injEq]; omega
      · ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Fin.ext_iff]
    have hb : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        aux_ko6_dN n (aux_ko6_tau n i) (aux_ko6_tau n (finRotate n i)) +
          (if (i.val = n - 1 ∨ i.val = (n - 1) / 2) then 1 else 0) ≤ 2 := by
      intro i _
      have h := aux_ko6_tau_dN n hn i
      split_ifs with hi
      · have := h.2 hi; omega
      · have := h.1; omega
    have := Finset.sum_le_sum hb
    rw [Finset.sum_add_distrib, Finset.sum_boole, hScard, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at this
    simp only [Nat.cast_ofNat] at this
    omega
  · have := aux_ko6_even n (by omega) _ (aux_ko6_tau_even n hn)
    omega

lemma aux_ko6_kopt (n : ℕ) (hn : 8 ≤ n) (k : ℕ) (hk : 4 * k ≤ n) (σ : Equiv.Perm (Fin n))
    (hσ : (tourEdges (aux_ko6_tau n) \ tourEdges σ).card = k) :
    2 * n - 2 ≤ ∑ e, aux_ko6_cnt σ e := by
  have hn2 : 2 ≤ n := by omega
  by_cases hpar : ∀ e, aux_ko6_cnt σ e % 2 = 0
  · have := aux_ko6_even n hn2 σ hpar
    omega
  push_neg at hpar
  obtain ⟨e0, he0⟩ := hpar
  have hodd : ∀ e, aux_ko6_cnt σ e % 2 = 1 := fun e => by
    have := aux_ko6_par n hn2 σ e e0; omega
  have hRIcard := aux_ko6_RI_card n (by omega) (aux_ko6_tau n) σ
  rw [hσ] at hRIcard
  set bad := (Finset.univ.filter (fun i => s(aux_ko6_tau n i, aux_ko6_tau n (finRotate n i))
      ∉ tourEdges σ)).biUnion (fun i => Finset.univ.filter (fun e : Fin n =>
        aux_ko6_arc n (aux_ko6_tau n i).val (aux_ko6_tau n (finRotate n i)).val e.val))
    with hbad
  have hbadcard : bad.card ≤ 2 * k := by
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_sum (fun i _ => (aux_ko6_tau_dN n hn i).1)) ?_
    rw [Finset.sum_const, smul_eq_mul, hRIcard, mul_comm]
  have hbase : (Finset.univ.filter (fun e : Fin n => 0 ≤ e.val ∧ e.val < n - 1)).card = n - 1 :=
    by rw [aux_ko6_card_Ico n 0 (n - 1) (by omega)]; rfl
  set G := (Finset.univ.filter (fun e : Fin n => 0 ≤ e.val ∧ e.val < n - 1)) \ bad with hG
  have hGcard : n - 1 - 2 * k ≤ G.card := by
    have h1 : (Finset.univ.filter (fun e : Fin n => 0 ≤ e.val ∧ e.val < n - 1)).card - bad.card
        ≤ G.card := Finset.le_card_sdiff _ _
    omega
  have hGcnt : ∀ e ∈ G, 3 ≤ aux_ko6_cnt σ e := by
    intro e he
    simp only [hG, hbad, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, not_exists, not_and] at he
    obtain ⟨he1, he2⟩ := he
    have hτc : 2 ≤ aux_ko6_cnt (aux_ko6_tau n) e := aux_ko6_tau_cnt n hn e he1.2
    have hle : aux_ko6_cnt (aux_ko6_tau n) e ≤ aux_ko6_cnt σ e := by
      unfold aux_ko6_cnt
      refine Finset.card_le_card_of_injOn (aux_ko6_J (aux_ko6_tau n) σ) ?_ ?_
      · intro i hi
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi ⊢
        have hmem : s(aux_ko6_tau n i, aux_ko6_tau n (finRotate n i)) ∈ tourEdges σ := by
          by_contra hc; exact he2 i hc hi
        exact (aux_ko6_arc_sym2 (aux_ko6_J_spec _ σ i hmem) e.val).mpr hi
      · intro i1 hi1 i2 hi2 heq
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi1 hi2
        have hm1 : s(aux_ko6_tau n i1, aux_ko6_tau n (finRotate n i1)) ∈ tourEdges σ := by
          by_contra hc; exact he2 i1 hc hi1
        have hm2 : s(aux_ko6_tau n i2, aux_ko6_tau n (finRotate n i2)) ∈ tourEdges σ := by
          by_contra hc; exact he2 i2 hc hi2
        have hs1 := aux_ko6_J_spec _ σ i1 hm1
        have hs2 := aux_ko6_J_spec _ σ i2 hm2
        rw [heq] at hs1
        exact aux_ko6_edge_inj n (by omega) (aux_ko6_tau n) (hs1.symm.trans hs2)
    have := hodd e
    omega
  have hb : ∀ e ∈ (Finset.univ : Finset (Fin n)),
      1 + 2 * (if e ∈ G then 1 else 0) ≤ aux_ko6_cnt σ e := by
    intro e _
    split_ifs with he
    · have := hGcnt e he; omega
    · have := hodd e; omega
  have := Finset.sum_le_sum hb
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id] at this
  omega

end TSPHeuristics.KOpt

open TSPHeuristics.KOpt

theorem solution (n : ℕ) (hn : 8 ≤ n) :
    ∃ d : Fin n → Fin n → ℝ, TSPHeuristics.Shared.IsTSPDist d ∧ 0 < TSPHeuristics.Shared.optimal d ∧
      ∃ τ : Equiv.Perm (Fin n), (∀ k : ℕ, 4 * k ≤ n → IsKOptimalTour d k τ) ∧
        TSPHeuristics.Shared.tourLength d τ = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d := by
  have hn2 : 2 ≤ n := by omega
  have hid : TSPHeuristics.Shared.tourLength (aux_ko6_d n) 1 = n := by
    unfold TSPHeuristics.Shared.tourLength aux_ko6_d
    simp only [Equiv.Perm.one_apply]
    have : ∀ j : Fin n, aux_ko6_dN n j (finRotate n j) = 1 := by
      intro j
      rw [aux_ko6_dN_eq, aux_ko6_fr]
      have := j.isLt
      split_ifs <;> omega
    simp only [this, Nat.cast_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have hopt : TSPHeuristics.Shared.optimal (aux_ko6_d n) = n := by
    apply le_antisymm
    · unfold TSPHeuristics.Shared.optimal
      rw [← hid]
      exact Finset.inf'_le _ (Finset.mem_univ _)
    · unfold TSPHeuristics.Shared.optimal
      apply Finset.le_inf'
      intro σ _
      rw [aux_ko6_len]
      exact_mod_cast aux_ko6_lower n hn2 σ
  have h2 : (2 : ℕ) ≤ 2 * n := by omega
  have hlen : TSPHeuristics.Shared.tourLength (aux_ko6_d n) (aux_ko6_tau n) = 2 * (n : ℝ) - 2 := by
    rw [aux_ko6_len, aux_ko6_tau_sum n hn]
    push_cast [Nat.cast_sub h2]
    ring
  refine ⟨aux_ko6_d n, aux_ko6_isTSP n, ?_, aux_ko6_tau n, ?_, ?_⟩
  · rw [hopt]; exact_mod_cast (by omega : 0 < n)
  · intro k hk σ hσ
    rw [hlen, aux_ko6_len]
    have := aux_ko6_kopt n hn k hk σ hσ
    calc (2 * (n : ℝ) - 2) = ((2 * n - 2 : ℕ) : ℝ) := by push_cast [Nat.cast_sub h2]; ring
      _ ≤ _ := by exact_mod_cast this
  · rw [hlen, hopt]
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
