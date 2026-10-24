-- Prove2me | solution 1 for PrizeAlloc.Param.converse
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T22:13:15.871677+00:00
-- url     : https://prove2.me/submissions/1f995de8-ae55-44a7-ac99-4194f6206846

import Mathlib
import Definitions.Def_PrizeAlloc_Param_Setting
import Definitions.Def_PrizeAlloc_Param_ParametricRule

set_option autoImplicit false
open PrizeAlloc.Interval PrizeAlloc.Param

namespace P3Conv

lemma sumIcc_eq_range (g : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, g k = ∑ k ∈ Finset.range n, g (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma sum_pos_eq {U : Type*} [DecidableEq U] (l : List U) (hl : l.Nodup) (g : ℕ → ℝ) :
    ∑ j ∈ l.toFinset, g (pos l j) = ∑ k ∈ Finset.Icc 1 l.length, g k := by
  rw [sumIcc_eq_range]
  induction l generalizing g with
  | nil => simp
  | cons a t ih =>
    have ha : a ∉ t := (List.nodup_cons.mp hl).1
    have ht := (List.nodup_cons.mp hl).2
    rw [List.toFinset_cons, Finset.sum_insert (by simpa using ha), List.length_cons,
      Finset.sum_range_succ']
    have h1 : ∑ j ∈ t.toFinset, g (pos (a :: t) j)
        = ∑ j ∈ t.toFinset, (fun k => g (k + 1)) (pos t j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hne : a ≠ j := fun h => ha (h ▸ List.mem_toFinset.mp hj)
      simp [pos, List.idxOf_cons_ne _ hne]
    rw [h1, ih ht (fun k => g (k + 1))]
    simp [pos, add_comm]

lemma pos_take {U : Type*} [DecidableEq U] (l : List U) (m : ℕ) (i : U) (hi : i ∈ l.take m) :
    pos (l.take m) i = pos l i := by
  unfold pos
  rw [(List.take_prefix m l).idxOf_eq_of_mem hi]

lemma sub_take {U : Type*} [DecidableEq U] (l : List U) (hl : l.Nodup) (m : ℕ) :
    sub l (l.take m).toFinset = l.take m := by
  unfold sub
  have hd : (l.take m ++ l.drop m).Nodup := by rw [List.take_append_drop]; exact hl
  have hsplit : List.filter (fun x => decide (x ∈ (l.take m).toFinset)) l
      = List.filter (fun x => decide (x ∈ (l.take m).toFinset)) (l.take m ++ l.drop m) := by
    rw [List.take_append_drop]
  rw [hsplit, List.filter_append, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr, List.append_nil]
  · intro x hx
    have := (List.nodup_append.mp hd).2.2
    simp only [List.mem_toFinset, decide_eq_true_eq]
    intro hx'
    exact this x hx' x hx rfl
  · intro x hx
    simpa using hx

end P3Conv

open P3Conv

theorem solution {U : Type*} [DecidableEq U]
    (φ : List U → ℝ → U → ℝ) (hφ : PrizeAlloc.Interval.IsPrizeRule φ) (hpar : IsParamRule φ) :
    PrizeAlloc.Interval.Anonymous φ ∧ PrizeAlloc.Interval.OrderPreserving φ ∧
      PrizeAlloc.Interval.WinnerStrictMonotone φ ∧ TopConsistent φ := by
  classical
  obtain ⟨f, ⟨hf1, hfk⟩, hrule⟩ := hpar
  -- the sum of the first `L` functions is strictly increasing
  have hSlt : ∀ L, 1 ≤ L → ∀ x y : ℝ, 0 ≤ x → x < y →
      ∑ k ∈ Finset.Icc 1 L, f k x < ∑ k ∈ Finset.Icc 1 L, f k y := by
    intro L hL x y hx hxy
    apply Finset.sum_lt_sum
    · intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      exact (hfk k hk1).2.1 (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (hx.trans hxy.le)) hxy.le
    · refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hL⟩, ?_⟩
      rw [hf1 x hx, hf1 y (hx.trans hxy.le)]
      exact hxy
  have hSinj : ∀ L, 1 ≤ L → ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      ∑ k ∈ Finset.Icc 1 L, f k x = ∑ k ∈ Finset.Icc 1 L, f k y → x = y := by
    intro L hL x y hx hy h
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · exact absurd h (hSlt L hL x y hx hxy).ne
    · exact hxy
    · exact absurd h (hSlt L hL y x hy hxy).ne'
  have hSrev : ∀ L, 1 ≤ L → ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      ∑ k ∈ Finset.Icc 1 L, f k x < ∑ k ∈ Finset.Icc 1 L, f k y → x < y := by
    intro L hL x y hx hy h
    by_contra hc
    push Not at hc
    rcases hc.lt_or_eq with hc | hc
    · exact absurd h (hSlt L hL y x hy hc).not_gt
    · rw [hc] at h; exact lt_irrefl _ h
  have hanti : ∀ k, 1 ≤ k → ∀ m, k ≤ m → ∀ x : ℝ, 0 ≤ x → f m x ≤ f k x := by
    intro k hk m hm x hx
    induction m, hm using Nat.le_induction with
    | base => exact le_rfl
    | succ m hkm ih => exact ((hfk m (hk.trans hkm)).2.2 x hx).2.trans ih
  have hlen : ∀ l : List U, IsRanking l → 1 ≤ l.length := by
    intro l hl
    exact List.length_pos_iff.mpr hl.2
  have hpos1 : ∀ (l : List U) (i : U), 1 ≤ pos l i := by
    intro l i; unfold pos; omega
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · -- anonymity
    intro l l' E hl hl' hE hll i hi j hj hij
    obtain ⟨x, hx, hxs, hxφ⟩ := hrule l E hl hE
    obtain ⟨x', hx', hxs', hxφ'⟩ := hrule l' E hl' hE
    rw [hll] at hxs
    have := hSinj l'.length (hlen l' hl') x x' hx hx' (hxs.trans hxs'.symm)
    rw [hxφ i hi, hxφ' j hj, hij, this]
  · -- order preservation
    intro l E hl hE i hi j hj hij
    obtain ⟨x, hx, -, hxφ⟩ := hrule l E hl hE
    rw [hxφ i hi, hxφ j hj]
    exact hanti _ (hpos1 l i) _ hij.le x hx
  · -- endowment monotonicity
    intro l E E' hl hE hEE i hi
    obtain ⟨x, hx, hxs, hxφ⟩ := hrule l E hl hE
    obtain ⟨x', hx', hxs', hxφ'⟩ := hrule l E' hl (hE.trans hEE.le)
    have hlt : x < x' := hSrev _ (hlen l hl) x x' hx hx' (by rw [hxs, hxs']; exact hEE)
    rw [hxφ i hi, hxφ' i hi]
    exact (hfk _ (hpos1 l i)).2.1 (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hx') hlt.le
  · -- strict for the winner
    intro l E E' hl hE hEE i hi hi1
    obtain ⟨x, hx, hxs, hxφ⟩ := hrule l E hl hE
    obtain ⟨x', hx', hxs', hxφ'⟩ := hrule l E' hl (hE.trans hEE.le)
    have hlt : x < x' := hSrev _ (hlen l hl) x x' hx hx' (by rw [hxs, hxs']; exact hEE)
    rw [hxφ i hi, hxφ' i hi, hi1, hf1 x hx, hf1 x' hx']
    exact hlt
  · -- top consistency
    intro l E hl hE S hS hSne hpos i hi
    obtain ⟨x, hx, hxs, hxφ⟩ := hrule l E hl hE
    set m := S.card with hm_def
    have hm1 : 1 ≤ m := Finset.card_pos.mpr hSne
    have hml : m ≤ l.length := by
      have := Finset.card_le_card hS
      rwa [List.toFinset_card_of_nodup hl.1] at this
    have hTlen : (l.take m).length = m := by simp [hml]
    have hSeq : S = (l.take m).toFinset := by
      apply Finset.eq_of_subset_of_card_le
      · intro j hj
        have hjl : j ∈ l := List.mem_toFinset.mp (hS hj)
        rw [List.mem_toFinset, List.mem_take_iff_idxOf_lt hjl]
        have := hpos j hj
        unfold pos at this
        omega
      · rw [List.toFinset_card_of_nodup ((List.take_sublist m l).nodup hl.1), hTlen]
    have hTr : IsRanking (l.take m) := by
      refine ⟨(List.take_sublist m l).nodup hl.1, ?_⟩
      intro h
      have := congrArg List.length h
      rw [hTlen] at this
      simp at this
      omega
    have hsum : ∑ j ∈ S, φ l E j = ∑ k ∈ Finset.Icc 1 m, f k x := by
      rw [← hTlen, ← sum_pos_eq (l.take m) hTr.1 (fun k => f k x), hSeq]
      apply Finset.sum_congr rfl
      intro j hj
      have hjT : j ∈ l.take m := List.mem_toFinset.mp hj
      rw [hxφ j ((List.take_sublist m l).subset hjT), pos_take l m j hjT]
    have hE' : 0 ≤ ∑ j ∈ S, φ l E j :=
      Finset.sum_nonneg (fun j hj => (hφ l E hl hE).1 j (List.mem_toFinset.mp (hS hj)))
    rw [hSeq, sub_take l hl.1 m]
    rw [hSeq] at hsum hE' hi
    obtain ⟨y, hy, hys, hyφ⟩ := hrule (l.take m) _ hTr hE'
    have hiT : i ∈ l.take m := List.mem_toFinset.mp hi
    rw [hyφ i hiT, hxφ i ((List.take_sublist m l).subset hiT), pos_take l m i hiT]
    rw [hsum, hTlen] at hys
    rw [hSinj m hm1 y x hy hx hys]
