-- Prove2me | solution 1 for PrizeAlloc.SingleParam.converse
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T22:13:37.569553+00:00
-- url     : https://prove2.me/submissions/72ade971-d8ae-47cb-b72e-8c35dd80aecb

import Mathlib
import Definitions.Def_PrizeAlloc_SingleParam_Setting
import Definitions.Def_PrizeAlloc_SingleParam_Rules

open PrizeAlloc.Interval PrizeAlloc.SingleParam

namespace SPLib

variable {U : Type*} [DecidableEq U]

/-! ## Positions in lists -/

lemma pos_getElem {l : List U} (hl : l.Nodup) (k : ℕ) (hk : k < l.length) :
    pos l l[k] = k + 1 := by
  unfold pos; rw [hl.idxOf_getElem]

lemma getElem_pos {l : List U} {i : U} (hi : i ∈ l) :
    ∃ h : pos l i - 1 < l.length, l[pos l i - 1] = i := by
  have := List.idxOf_lt_length_of_mem hi
  refine ⟨by unfold pos; omega, ?_⟩
  simp [pos]

lemma one_le_pos (l : List U) (i : U) : 1 ≤ pos l i := by unfold pos; omega

lemma pos_le_length {l : List U} {i : U} (hi : i ∈ l) : pos l i ≤ l.length := by
  unfold pos; have := List.idxOf_lt_length_of_mem hi; omega

lemma sum_pos (F : ℕ → ℝ) : ∀ (l : List U), l.Nodup →
    ∑ i ∈ l.toFinset, F (pos l i) = ∑ k ∈ Finset.range l.length, F (k + 1)
  | [], _ => by simp
  | a :: t, hl => by
    have ha : a ∉ t := (List.nodup_cons.1 hl).1
    have ht := (List.nodup_cons.1 hl).2
    rw [List.toFinset_cons, Finset.sum_insert (by simpa using ha), List.length_cons,
      Finset.sum_range_succ']
    have : ∑ i ∈ t.toFinset, F (pos (a :: t) i) = ∑ i ∈ t.toFinset, F (pos t i + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hne : a ≠ i := fun h => ha (h ▸ List.mem_toFinset.1 hi)
      unfold pos; rw [List.idxOf_cons_ne _ hne]
    rw [this, sum_pos (fun k => F (k + 1)) t ht]
    simp [pos, add_comm]

lemma idxOf_lt_of_mem_take {l : List U} {m : ℕ} {j : U} (hj : j ∈ l.take m) :
    l.idxOf j < m := by
  have h1 : l.idxOf j = (l.take m).idxOf j := by
    conv_lhs => rw [← List.take_append_drop m l]
    exact List.idxOf_append_of_mem hj
  have h2 := List.idxOf_lt_length_of_mem hj
  have h3 := List.length_take_le m l
  omega

lemma le_idxOf_of_mem_drop {l : List U} (hl : l.Nodup) {m : ℕ} {j : U} (hj : j ∈ l.drop m) :
    m ≤ l.idxOf j := by
  have hnot : j ∉ l.take m := by
    intro h
    have hd := List.disjoint_take_drop hl (le_refl m)
    exact hd h hj
  have hlen : m < l.length := by
    have := List.length_pos_of_mem hj
    simp at this; omega
  have h1 : l.idxOf j = (l.take m).length + (l.drop m).idxOf j := by
    conv_lhs => rw [← List.take_append_drop m l]
    exact List.idxOf_append_of_notMem hnot
  rw [h1, List.length_take]; omega

/-- Positions in a block of consecutive positions shift by a constant in the subranking. -/
lemma block_pos {l : List U} (hl : l.Nodup) (S : Finset U) (hS : S ⊆ l.toFinset)
    (hne : S.Nonempty)
    (hgap : ∀ i ∈ S, ∀ j ∈ S, pos l i ≤ pos l j + (S.card - 1)) :
    ∃ m, ∀ i ∈ S, pos l i = m + pos (sub l S) i := by
  obtain ⟨j0, hj0S, hj0min⟩ := S.exists_min_image (fun j => l.idxOf j) hne
  set m := l.idxOf j0 with hm
  set c := S.card with hc
  have hc1 : 1 ≤ c := Finset.card_pos.2 hne
  have hmem : ∀ i ∈ S, i ∈ l := fun i hi => List.mem_toFinset.1 (hS hi)
  have hrange : ∀ i ∈ S, m ≤ l.idxOf i ∧ l.idxOf i + 1 ≤ m + c := by
    intro i hi; refine ⟨hj0min i hi, ?_⟩
    have := hgap i hi j0 hj0S; unfold pos at this
    omega
  have hmlen : m < l.length := List.idxOf_lt_length_of_mem (hmem j0 hj0S)
  set A := l.take m
  set B := (l.drop m).take c
  set C := l.drop (m + c)
  have hsplit : l = A ++ (B ++ C) := by
    simp only [A, B, C]
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have hA : ∀ j ∈ A, j ∉ S := by
    intro j hj hjS
    have := idxOf_lt_of_mem_take hj
    have := (hrange j hjS).1
    omega
  have hC : ∀ j ∈ C, j ∉ S := by
    intro j hj hjS
    have := le_idxOf_of_mem_drop hl hj
    have := (hrange j hjS).2
    omega
  have hSB : S ⊆ B.toFinset := by
    intro i hi
    have hil : i ∈ l := hmem i hi
    rw [hsplit] at hil
    rcases List.mem_append.1 hil with h | h
    · exact absurd hi (hA i h)
    rcases List.mem_append.1 h with h | h
    · exact List.mem_toFinset.2 h
    · exact absurd hi (hC i h)
  have hBlen : B.length ≤ c := List.length_take_le _ _
  have hBS : B.toFinset = S := by
    symm
    apply Finset.eq_of_subset_of_card_le hSB
    calc B.toFinset.card ≤ B.length := List.toFinset_card_le B
      _ ≤ c := hBlen
  have hBmem : ∀ j ∈ B, j ∈ S := by
    intro j hj; rw [← hBS]; exact List.mem_toFinset.2 hj
  have hsub : sub l S = B := by
    unfold sub
    rw [hsplit, List.filter_append, List.filter_append]
    have h1 : A.filter (fun x => decide (x ∈ S)) = [] := by
      rw [List.filter_eq_nil_iff]; intro a ha; simpa using hA a ha
    have h2 : C.filter (fun x => decide (x ∈ S)) = [] := by
      rw [List.filter_eq_nil_iff]; intro a ha; simpa using hC a ha
    have h3 : B.filter (fun x => decide (x ∈ S)) = B := by
      rw [List.filter_eq_self]; intro a ha; simpa using hBmem a ha
    rw [h1, h2, h3]; simp
  refine ⟨m, fun i hi => ?_⟩
  rw [hsub]
  have hiB : i ∈ B := List.mem_toFinset.1 (hSB hi)
  have hAlen : A.length = m := by simp [A]; omega
  unfold pos
  conv_lhs => rw [hsplit]
  rw [List.idxOf_append_of_notMem (fun h => hA i h hi), List.idxOf_append_of_mem hiB, hAlen]
  omega

lemma sub_nodup {l : List U} (hl : l.Nodup) (S : Finset U) : (sub l S).Nodup :=
  hl.filter _

lemma sub_toFinset {l : List U} (S : Finset U) (hS : S ⊆ l.toFinset) :
    (sub l S).toFinset = S := by
  ext i; simp only [sub, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨List.mem_toFinset.1 (hS h), h⟩

lemma sub_length {l : List U} (hl : l.Nodup) (S : Finset U) (hS : S ⊆ l.toFinset) :
    (sub l S).length = S.card := by
  have := List.toFinset_card_of_nodup (sub_nodup hl S)
  rw [sub_toFinset S hS] at this
  exact this.symm

/-! ## Iterates of a representation -/

section Iter
variable {f : ℝ → ℝ}

lemma f_zero (hf : IsRepresentation f) : f 0 = 0 :=
  le_antisymm (hf.2.2 0 le_rfl).2 (hf.2.2 0 le_rfl).1

lemma iter_zero (hf : IsRepresentation f) (n : ℕ) : f^[n] 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, f_zero hf]

lemma iter_nonneg (hf : IsRepresentation f) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f^[n] x := by
  induction n with
  | zero => exact hx
  | succ n ih => rw [Function.iterate_succ_apply']; exact (hf.2.2 _ ih).1

lemma iter_le (hf : IsRepresentation f) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : f^[n] x ≤ x := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ((hf.2.2 _ (iter_nonneg hf n hx)).2).trans ih

lemma iter_mono (hf : IsRepresentation f) (n : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    f^[n] x ≤ f^[n] y := by
  induction n with
  | zero => exact hxy
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hf.2.1 (Set.mem_Ici.2 (iter_nonneg hf n hx))
      (Set.mem_Ici.2 (iter_nonneg hf n (hx.trans hxy))) ih

lemma iter_anti (hf : IsRepresentation f) {a b : ℕ} (hab : a ≤ b) {x : ℝ} (hx : 0 ≤ x) :
    f^[b] x ≤ f^[a] x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [add_comm, Function.iterate_add_apply]
  exact iter_le hf d (iter_nonneg hf a hx)

lemma iter_cont (hf : IsRepresentation f) (n : ℕ) : ContinuousOn (f^[n]) (Set.Ici 0) := by
  induction n with
  | zero => exact continuousOn_id
  | succ n ih =>
    rw [Function.iterate_succ']
    exact hf.1.comp ih (fun x hx => Set.mem_Ici.2 (iter_nonneg hf n (Set.mem_Ici.1 hx)))

/-- The total prize `∑_{k<n} f^[k] x`. -/
lemma total_strictMonoOn (hf : IsRepresentation f) {n : ℕ} (hn : 0 < n) :
    StrictMonoOn (fun x => ∑ k ∈ Finset.range n, f^[k] x) (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only
  apply Finset.sum_lt_sum
  · intro k _; exact iter_mono hf k hx hxy.le
  · exact ⟨0, Finset.mem_range.2 hn, hxy⟩

lemma total_inj (hf : IsRepresentation f) {n : ℕ} (hn : 0 < n) {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) (h : ∑ k ∈ Finset.range n, f^[k] x = ∑ k ∈ Finset.range n, f^[k] y) :
    x = y :=
  (total_strictMonoOn hf hn).injOn hx hy h

lemma total_cont (hf : IsRepresentation f) (n : ℕ) :
    ContinuousOn (fun x => ∑ k ∈ Finset.range n, f^[k] x) (Set.Ici 0) :=
  continuousOn_finsetSum _ (fun k _ => iter_cont hf k)

lemma total_exists (hf : IsRepresentation f) {n : ℕ} (hn : 0 < n) {E : ℝ} (hE : 0 ≤ E) :
    ∃ x, 0 ≤ x ∧ ∑ k ∈ Finset.range n, f^[k] x = E := by
  have hc : ContinuousOn (fun x => ∑ k ∈ Finset.range n, f^[k] x) (Set.Icc 0 E) :=
    (total_cont hf n).mono Set.Icc_subset_Ici_self
  have h0 : ∑ k ∈ Finset.range n, f^[k] (0 : ℝ) = 0 := by simp [iter_zero hf]
  have hE' : E ≤ ∑ k ∈ Finset.range n, f^[k] E := by
    obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_lt hn
    rw [show 0 + n' + 1 = n' + 1 by omega, Finset.sum_range_succ']
    simp only [Function.iterate_zero, id]
    have : 0 ≤ ∑ k ∈ Finset.range n', f^[k + 1] E :=
      Finset.sum_nonneg (fun k _ => iter_nonneg hf _ hE)
    linarith
  obtain ⟨x, hx, hxE⟩ := intermediate_value_Icc hE hc ⟨by rw [h0]; exact hE, hE'⟩
  exact ⟨x, hx.1, hxE⟩

end Iter

/-! ## Single-parametric rules satisfy the axioms -/

section Converse
variable {f : ℝ → ℝ} {φ : List U → ℝ → U → ℝ}

lemma ranking_length_pos {l : List U} (hl : IsRanking l) : 0 < l.length :=
  List.length_pos_iff.2 hl.2

theorem conv_anonymous (hf : IsRepresentation f) (h : IsSingleParamRuleWith f φ) :
    Anonymous φ := by
  intro l l' E hl hl' hE hlen i hi j hj hij
  obtain ⟨x, hx, hxs, hxφ⟩ := h l E hl hE
  obtain ⟨x', hx', hxs', hxφ'⟩ := h l' E hl' hE
  have : x = x' := total_inj hf (ranking_length_pos hl) hx hx' (by rw [hxs, hlen, hxs'])
  rw [hxφ i hi, hxφ' j hj, hij, this]

theorem conv_orderPreserving (hf : IsRepresentation f) (h : IsSingleParamRuleWith f φ) :
    OrderPreserving φ := by
  intro l E hl hE i hi j hj hij
  obtain ⟨x, hx, _, hxφ⟩ := h l E hl hE
  rw [hxφ i hi, hxφ j hj]
  exact iter_anti hf (by omega) hx

lemma conv_lt (hf : IsRepresentation f) (h : IsSingleParamRuleWith f φ) {l : List U}
    (hl : IsRanking l) {E E' x x' : ℝ} (hE : 0 ≤ E) (hEE' : E < E') (hx : 0 ≤ x) (hx' : 0 ≤ x')
    (hxs : ∑ k ∈ Finset.range l.length, f^[k] x = E)
    (hxs' : ∑ k ∈ Finset.range l.length, f^[k] x' = E') : x < x' := by
  by_contra hcon
  push Not at hcon
  have := (total_strictMonoOn hf (ranking_length_pos hl)).monotoneOn hx' hx hcon
  linarith

theorem conv_winnerStrictMonotone (hf : IsRepresentation f) (h : IsSingleParamRuleWith f φ) :
    WinnerStrictMonotone φ := by
  refine ⟨?_, ?_⟩
  · intro l E E' hl hE hEE' i hi
    obtain ⟨x, hx, hxs, hxφ⟩ := h l E hl hE
    obtain ⟨x', hx', hxs', hxφ'⟩ := h l E' hl (hE.trans hEE'.le)
    have hlt := conv_lt hf h hl hE hEE' hx hx' hxs hxs'
    rw [hxφ i hi, hxφ' i hi]
    exact iter_mono hf _ hx hlt.le
  · intro l E E' hl hE hEE' i hi hpos
    obtain ⟨x, hx, hxs, hxφ⟩ := h l E hl hE
    obtain ⟨x', hx', hxs', hxφ'⟩ := h l E' hl (hE.trans hEE'.le)
    have hlt := conv_lt hf h hl hE hEE' hx hx' hxs hxs'
    rw [hxφ i hi, hxφ' i hi, hpos]
    simpa using hlt

theorem conv_locallyConsistent (hf : IsRepresentation f) (h : IsSingleParamRuleWith f φ) :
    LocallyConsistent φ := by
  intro l E hl hE S hS hgap i hi
  have hne : S.Nonempty := ⟨i, hi⟩
  obtain ⟨m, hm⟩ := block_pos hl.1 S hS hne hgap
  obtain ⟨x, hx, hxs, hxφ⟩ := h l E hl hE
  have hmemS : ∀ j ∈ S, j ∈ l := fun j hj => List.mem_toFinset.1 (hS hj)
  set l' := sub l S
  have hl' : IsRanking l' := by
    refine ⟨sub_nodup hl.1 S, ?_⟩
    intro h0
    have : i ∈ l'.toFinset := by rw [sub_toFinset S hS]; exact hi
    rw [h0] at this; simp at this
  set E' := ∑ j ∈ S, φ l E j
  have hE' : 0 ≤ E' := by
    obtain ⟨x0, hx0, _, hx0φ⟩ := h l E hl hE
    exact Finset.sum_nonneg (fun j hj => by rw [hx0φ j (hmemS j hj)]; exact iter_nonneg hf _ hx0)
  obtain ⟨y, hy, hys, hyφ⟩ := h l' E' hl' hE'
  -- the sum E' equals the total of the shifted parameter
  have hshift : ∀ j ∈ S, φ l E j = f^[pos l' j - 1] (f^[m] x) := by
    intro j hj
    rw [hxφ j (hmemS j hj), ← Function.iterate_add_apply, hm j hj]
    congr 1
    have := one_le_pos l' j
    omega
  have hE'eq : E' = ∑ k ∈ Finset.range l'.length, f^[k] (f^[m] x) := by
    have h1 : E' = ∑ j ∈ l'.toFinset, f^[pos l' j - 1] (f^[m] x) := by
      rw [sub_toFinset S hS]; exact Finset.sum_congr rfl hshift
    rw [h1, sum_pos (fun k => f^[k - 1] (f^[m] x)) l' hl'.1]
    simp
  have hyx : y = f^[m] x :=
    total_inj hf (ranking_length_pos hl') hy (iter_nonneg hf m hx) (by rw [hys, hE'eq])
  have hil' : i ∈ l' := by
    rw [← List.mem_toFinset, sub_toFinset S hS]; exact hi
  rw [hyφ i hil', hyx, hshift i hi]

theorem converse_main (φ : List U → ℝ → U → ℝ) (h : IsSingleParamRule φ) :
    Anonymous φ ∧ OrderPreserving φ ∧ WinnerStrictMonotone φ ∧ LocallyConsistent φ := by
  obtain ⟨f, hf, h⟩ := h
  exact ⟨conv_anonymous hf h, conv_orderPreserving hf h, conv_winnerStrictMonotone hf h,
    conv_locallyConsistent hf h⟩

end Converse

/-! ## The chain argument -/

section Chain
variable {f : ℝ → ℝ} {φ : List U → ℝ → U → ℝ}

theorem chain_step (hφ : IsPrizeRule φ) (hLC : LocallyConsistent φ)
    (h2 : ∀ l E, IsRanking l → l.length = 2 → 0 ≤ E →
      ∃ x, 0 ≤ x ∧ (∑ k ∈ Finset.range l.length, f^[k] x) = E ∧
        ∀ i ∈ l, φ l E i = f^[pos l i - 1] x)
    {l : List U} (hl : IsRanking l) {E : ℝ} (hE : 0 ≤ E) (k : ℕ) (hk : k + 1 < l.length) :
    φ l E l[k + 1] = f (φ l E l[k]) := by
  have hne : l[k] ≠ l[k + 1] := by
    intro h
    have := (hl.1.getElem_inj_iff).1 h
    omega
  set S : Finset U := {l[k], l[k + 1]} with hSdef
  have hScard : S.card = 2 := Finset.card_pair hne
  have hS : S ⊆ l.toFinset := by
    intro j hj
    simp only [hSdef, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> simp
  have hpk : pos l l[k] = k + 1 := pos_getElem hl.1 k (by omega)
  have hpk1 : pos l l[k + 1] = k + 2 := pos_getElem hl.1 (k + 1) hk
  have hgap : ∀ i ∈ S, ∀ j ∈ S, pos l i ≤ pos l j + (S.card - 1) := by
    intro i hi j hj
    rw [hScard]
    simp only [hSdef, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> omega
  have hkS : l[k] ∈ S := by simp [hSdef]
  have hk1S : l[k + 1] ∈ S := by simp [hSdef]
  obtain ⟨m, hm⟩ := block_pos hl.1 S hS ⟨_, hkS⟩ hgap
  set l' := sub l S
  have hl'len : l'.length = 2 := by rw [sub_length hl.1 S hS, hScard]
  have hl' : IsRanking l' := ⟨sub_nodup hl.1 S, by intro h0; rw [h0] at hl'len; simp at hl'len⟩
  have hkl' : l[k] ∈ l' := by rw [← List.mem_toFinset, sub_toFinset S hS]; exact hkS
  have hk1l' : l[k + 1] ∈ l' := by rw [← List.mem_toFinset, sub_toFinset S hS]; exact hk1S
  have h1 := hm _ hkS
  have h2' := hm _ hk1S
  have b1 := one_le_pos l' l[k]
  have b2 := one_le_pos l' l[k + 1]
  have c1 := pos_le_length hkl'
  have c2 := pos_le_length hk1l'
  have hp1 : pos l' l[k] = 1 := by omega
  have hp2 : pos l' l[k + 1] = 2 := by omega
  set E' := ∑ j ∈ S, φ l E j
  have hE' : 0 ≤ E' := Finset.sum_nonneg (fun j hj =>
    (hφ l E hl hE).1 j (List.mem_toFinset.1 (hS hj)))
  obtain ⟨x, _, _, hxφ⟩ := h2 l' E' hl' hl'len hE'
  have e1 := hLC l E hl hE S hS hgap _ hkS
  have e2 := hLC l E hl hE S hS hgap _ hk1S
  rw [e1, e2, hxφ _ hkl', hxφ _ hk1l', hp1, hp2]
  rfl

theorem chain_iter (hφ : IsPrizeRule φ) (hLC : LocallyConsistent φ)
    (h2 : ∀ l E, IsRanking l → l.length = 2 → 0 ≤ E →
      ∃ x, 0 ≤ x ∧ (∑ k ∈ Finset.range l.length, f^[k] x) = E ∧
        ∀ i ∈ l, φ l E i = f^[pos l i - 1] x)
    {l : List U} (hl : IsRanking l) {E : ℝ} (hE : 0 ≤ E) (q : ℕ) :
    ∀ (d : ℕ) (hd : q + d < l.length), φ l E l[q + d] = f^[d] (φ l E (l[q]'(by omega)))
  | 0, _ => rfl
  | d + 1, hd => by
    have := chain_step hφ hLC h2 hl hE (q + d) (by omega)
    rw [Function.iterate_succ_apply', ← chain_iter hφ hLC h2 hl hE q d (by omega), ← this]
    rfl

theorem chain_singleParam (hφ : IsPrizeRule φ) (hLC : LocallyConsistent φ)
    (h2 : ∀ l E, IsRanking l → l.length = 2 → 0 ≤ E →
      ∃ x, 0 ≤ x ∧ (∑ k ∈ Finset.range l.length, f^[k] x) = E ∧
        ∀ i ∈ l, φ l E i = f^[pos l i - 1] x) :
    IsSingleParamRuleWith f φ := by
  intro l E hl hE
  have hlen := ranking_length_pos hl
  set x := φ l E (l[0]'hlen)
  have hform : ∀ i ∈ l, φ l E i = f^[pos l i - 1] x := by
    intro i hi
    obtain ⟨hlt, hget⟩ := getElem_pos hi
    have := chain_iter hφ hLC h2 hl hE 0 (pos l i - 1) (by omega)
    simp only [zero_add] at this
    rw [hget] at this
    exact this
  refine ⟨x, (hφ l E hl hE).1 _ (List.getElem_mem _), ?_, hform⟩
  have hsum := (hφ l E hl hE).2
  rw [← hsum, Finset.sum_congr rfl (fun i hi => hform i (List.mem_toFinset.1 hi)),
    sum_pos (fun k => f^[k - 1] x) l hl.1]
  simp

end Chain


/-! ## Two competitors -/

section Two
variable {φ : List U → ℝ → U → ℝ}

theorem rep_f (hφ : IsPrizeRule φ) (hOP : OrderPreserving φ)
    (hW : WinnerStrictMonotone φ) (hC : EndowmentContinuous φ) (u v : U) (huv : u ≠ v) :
    ∃ f : ℝ → ℝ, IsRepresentation f ∧
      (∀ x, 0 ≤ x → φ [u, v] (x + f x) u = x ∧ φ [u, v] (x + f x) v = f x) ∧
      (∀ x y, 0 ≤ x → 0 ≤ y → φ [u, v] (x + y) u = x → φ [u, v] (x + y) v = y → y = f x) := by
  set l2 : List U := [u, v]
  have hl2 : IsRanking l2 := ⟨by simp [l2, huv], by simp [l2]⟩
  have hu : u ∈ l2 := by simp [l2]
  have hv : v ∈ l2 := by simp [l2]
  have hpu : pos l2 u = 1 := by simp [pos, l2]
  have hpv : pos l2 v = 2 := by simp [pos, l2, List.idxOf_cons_ne _ huv]
  have hsum : ∀ E, 0 ≤ E → φ l2 E u + φ l2 E v = E := by
    intro E hE
    have := (hφ l2 E hl2 hE).2
    rwa [show l2.toFinset = {u, v} by simp [l2], Finset.sum_pair huv] at this
  have hnu : ∀ E, 0 ≤ E → 0 ≤ φ l2 E u := fun E hE => (hφ l2 E hl2 hE).1 u hu
  have hnv : ∀ E, 0 ≤ E → 0 ≤ φ l2 E v := fun E hE => (hφ l2 E hl2 hE).1 v hv
  have hop : ∀ E, 0 ≤ E → φ l2 E v ≤ φ l2 E u := fun E hE =>
    hOP l2 E hl2 hE u hu v hv (by rw [hpu, hpv]; norm_num)
  set g : ℝ → ℝ := fun E => φ l2 E u
  have hg0 : g 0 = 0 := by
    have := hsum 0 le_rfl; have := hnu 0 le_rfl; have := hnv 0 le_rfl
    simp only [g]; linarith
  have hgs : ∀ E E', 0 ≤ E → E < E' → g E < g E' := fun E E' hE hEE' =>
    hW.2 l2 E E' hl2 hE hEE' u hu hpu
  set G : ℝ → ℝ := fun x => if 0 ≤ x then g x else x
  have hGmono : StrictMono G := by
    intro x y hxy
    simp only [G]
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, if_pos (hx.trans hxy.le)]; exact hgs x y hx hxy
    · rw [if_neg hx]
      by_cases hy : 0 ≤ y
      · rw [if_pos hy]; have := hnu y hy; simp only [g]; push Not at hx; linarith
      · rw [if_neg hy]; exact hxy
  have hGsurj : Function.Surjective G := by
    intro y
    by_cases hy : 0 ≤ y
    · have hc : ContinuousOn g (Set.Icc 0 (2 * y)) :=
        (hC l2 hl2 u hu).mono Set.Icc_subset_Ici_self
      have h2y : y ≤ g (2 * y) := by
        have := hsum (2 * y) (by linarith); have := hop (2 * y) (by linarith)
        simp only [g]; linarith
      obtain ⟨E, hE, hgE⟩ := intermediate_value_Icc (by linarith) hc ⟨by rw [hg0]; exact hy, h2y⟩
      exact ⟨E, by simp only [G]; rw [if_pos hE.1]; exact hgE⟩
    · exact ⟨y, by simp only [G]; rw [if_neg hy]⟩
  set e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective G hGmono hGsurj
  have he : ∀ x, e x = G x := fun x => rfl
  set h : ℝ → ℝ := ⇑e.symm with hhdef
  have hGh : ∀ x, G (h x) = x := fun x => by rw [← he]; exact e.apply_symm_apply x
  have hh0 : ∀ x, 0 ≤ x → 0 ≤ h x := by
    intro x hx
    by_contra hneg
    have := hGh x
    simp only [G] at this
    rw [if_neg hneg] at this
    push Not at hneg; linarith
  have hgh : ∀ x, 0 ≤ x → g (h x) = x := by
    intro x hx
    have := hGh x
    simp only [G] at this
    rwa [if_pos (hh0 x hx)] at this
  have hhG : ∀ E, h (G E) = E := fun E => by rw [← he]; exact e.symm_apply_apply E
  refine ⟨fun x => h x - x, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (e.symm.continuous.sub continuous_id).continuousOn
  · intro x hx y hy hxy
    simp only
    have hx' := Set.mem_Ici.1 hx
    have hy' := Set.mem_Ici.1 hy
    have ex : h x - x = φ l2 (h x) v := by
      have := hsum (h x) (hh0 x hx'); have := hgh x hx'; simp only [g] at *; linarith
    have ey : h y - y = φ l2 (h y) v := by
      have := hsum (h y) (hh0 y hy'); have := hgh y hy'; simp only [g] at *; linarith
    rw [ex, ey]
    rcases (e.symm.monotone hxy).lt_or_eq with hlt | heq
    · exact hW.1 l2 (h x) (h y) hl2 (hh0 x hx') hlt v hv
    · simp only [h] at *; rw [heq]
  · intro x hx
    have := hsum (h x) (hh0 x hx); have := hgh x hx
    have := hnv (h x) (hh0 x hx); have := hop (h x) (hh0 x hx)
    simp only [g] at *
    constructor <;> linarith
  · intro x hx
    have e1 : x + (h x - x) = h x := by ring
    have := hsum (h x) (hh0 x hx); have := hgh x hx
    simp only [g] at *
    rw [e1]
    constructor <;> linarith
  · intro x y hx hy hu' hv'
    have hG : G (x + y) = x := by
      simp only [G]; rw [if_pos (by linarith)]; exact hu'
    have := hhG (x + y)
    rw [hG] at this
    simp only
    linarith

theorem two_form (hφ : IsPrizeRule φ) (hA : Anonymous φ) (hOP : OrderPreserving φ)
    (hW : WinnerStrictMonotone φ) (hC : EndowmentContinuous φ) :
    ∃ f : ℝ → ℝ, IsRepresentation f ∧
      ∀ l E, IsRanking l → l.length = 2 → 0 ≤ E →
        ∃ x, 0 ≤ x ∧ (∑ k ∈ Finset.range l.length, f^[k] x) = E ∧
          ∀ i ∈ l, φ l E i = f^[pos l i - 1] x := by
  by_cases hex : ∃ u v : U, u ≠ v
  · obtain ⟨u, v, huv⟩ := hex
    obtain ⟨f, hf, hfwd, hbwd⟩ := rep_f hφ hOP hW hC u v huv
    refine ⟨f, hf, ?_⟩
    intro l E hl hlen hE
    match l, hl, hlen with
    | [a, b], hl, _ =>
      have hab : a ≠ b := by have := hl.1; simpa using this
      have hl2 : IsRanking [u, v] := ⟨by simp [huv], by simp⟩
      have hpa : pos [a, b] a = 1 := by simp [pos]
      have hpb : pos [a, b] b = 2 := by simp [pos, List.idxOf_cons_ne _ hab]
      have hpu : pos [u, v] u = 1 := by simp [pos]
      have hpv : pos [u, v] v = 2 := by simp [pos, List.idxOf_cons_ne _ huv]
      have ea : φ [a, b] E a = φ [u, v] E u :=
        hA [a, b] [u, v] E hl hl2 hE rfl a (by simp) u (by simp) (by rw [hpa, hpu])
      have eb : φ [a, b] E b = φ [u, v] E v :=
        hA [a, b] [u, v] E hl hl2 hE rfl b (by simp) v (by simp) (by rw [hpb, hpv])
      have hsum : φ [u, v] E u + φ [u, v] E v = E := by
        have := (hφ [u, v] E hl2 hE).2
        rwa [show [u, v].toFinset = {u, v} by simp, Finset.sum_pair huv] at this
      have hnu := (hφ [u, v] E hl2 hE).1 u (by simp)
      have hnv := (hφ [u, v] E hl2 hE).1 v (by simp)
      have hy := hbwd (φ [u, v] E u) (φ [u, v] E v) hnu hnv (by rw [hsum]) (by rw [hsum])
      refine ⟨φ [u, v] E u, hnu, ?_, ?_⟩
      · simp [Finset.sum_range_succ, ← hy, hsum]
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · rw [hpa, ea]; rfl
        · rw [hpb, eb, hy]; rfl
  · push Not at hex
    refine ⟨id, ⟨continuousOn_id, monotoneOn_id, fun x hx => ⟨hx, le_rfl⟩⟩, ?_⟩
    intro l E hl hlen hE
    match l, hl, hlen with
    | [a, b], hl, _ =>
      have : a ≠ b := by have := hl.1; simpa using this
      exact absurd (hex a b) this

end Two

/-! ## Uniqueness and propagation -/

section Uniq
variable {f : ℝ → ℝ} {φ φ' : List U → ℝ → U → ℝ}

theorem uniq (hφ : IsPrizeRule φ) (hLC : LocallyConsistent φ) (hf : IsRepresentation f)
    (h2 : ∀ l E, IsRanking l → l.length = 2 → 0 ≤ E →
      ∃ x, 0 ≤ x ∧ (∑ k ∈ Finset.range l.length, f^[k] x) = E ∧
        ∀ i ∈ l, φ l E i = f^[pos l i - 1] x)
    (h' : IsSingleParamRuleWith f φ') :
    ∀ l E, IsRanking l → 0 ≤ E → ∀ i ∈ l, φ' l E i = φ l E i := by
  intro l E hl hE i hi
  obtain ⟨x, hx, hxs, hxφ⟩ := chain_singleParam hφ hLC h2 l E hl hE
  obtain ⟨x', hx', hxs', hxφ'⟩ := h' l E hl hE
  have : x' = x := total_inj hf (ranking_length_pos hl) hx' hx (by rw [hxs, hxs'])
  rw [hxφ i hi, hxφ' i hi, this]

theorem propag (hφ : IsPrizeRule φ) (hLC : LocallyConsistent φ) (hf : IsRepresentation f)
    (h2 : ∀ l E, IsRanking l → l.length = 2 → 0 ≤ E →
      ∃ x, 0 ≤ x ∧ (∑ k ∈ Finset.range l.length, f^[k] x) = E ∧
        ∀ i ∈ l, φ l E i = f^[pos l i - 1] x)
    (h' : IsSingleParamRuleWith f φ')
    (l : List U) (hl : IsRanking l) (E : ℝ) (hE : 0 ≤ E) (q : ℕ) (hq : q < l.length)
    (hgt : φ l E l[q] < φ' l E l[q]) :
    ∀ r (hr : r < l.length), q < r → φ l E l[r] ≤ φ' l E l[r] := by
  intro r hr hqr
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hqr
  have e1 := chain_iter hφ hLC h2 hl hE q (d + 1) (by omega)
  obtain ⟨x', hx', _, hxφ'⟩ := h' l E hl hE
  have e2 : φ' l E l[q + (d + 1)] = f^[d + 1] (φ' l E l[q]) := by
    rw [hxφ' _ (List.getElem_mem _), hxφ' _ (List.getElem_mem _), pos_getElem hl.1 _ (by omega),
      pos_getElem hl.1 _ hq, ← Function.iterate_add_apply]
    congr 1; omega
  have hn : 0 ≤ φ l E l[q] := (hφ l E hl hE).1 _ (List.getElem_mem _)
  have : q + d + 1 = q + (d + 1) := by omega
  simp only [this]
  rw [e1, e2]
  exact iter_mono hf _ hn hgt.le

end Uniq

end SPLib


theorem solution {U : Type*} [DecidableEq U]
    (φ : List U → ℝ → U → ℝ) (hφ : PrizeAlloc.Interval.IsPrizeRule φ) (h : IsSingleParamRule φ) :
    PrizeAlloc.Interval.Anonymous φ ∧ PrizeAlloc.Interval.OrderPreserving φ ∧ PrizeAlloc.Interval.WinnerStrictMonotone φ ∧ LocallyConsistent φ :=
  SPLib.converse_main φ h
