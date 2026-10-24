-- Prove2me | solution 1 for PrizeAlloc.Param.induction_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T22:16:31.085665+00:00
-- url     : https://prove2.me/submissions/063f5af8-dbf4-4ffa-8a14-5615d9e32b0b

import Mathlib
import Definitions.Def_PrizeAlloc_Param_Setting
import Definitions.Def_PrizeAlloc_Param_ParametricRule
import Theorems.Thm_PrizeAlloc_Param_winner_prize_inverse

set_option autoImplicit false
open PrizeAlloc.Interval PrizeAlloc.Param

namespace P3Ind

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


lemma posGet {U : Type*} [DecidableEq U] (l : List U) (hl : l.Nodup) (k : ℕ) (hk : k < l.length) :
    pos l l[k] = k + 1 := by
  unfold pos
  rw [List.Nodup.idxOf_getElem hl k hk]

end P3Ind

open P3Ind

theorem solution {U : Type*} [DecidableEq U]
    (φ : List U → ℝ → U → ℝ) (hφ : PrizeAlloc.Interval.IsPrizeRule φ)
    (hA : PrizeAlloc.Interval.Anonymous φ) (hOP : PrizeAlloc.Interval.OrderPreserving φ) (hWSM : PrizeAlloc.Interval.WinnerStrictMonotone φ)
    (hTC : TopConsistent φ) (hEC : PrizeAlloc.Interval.EndowmentContinuous φ)
    (n : ℕ) (hn : 1 ≤ n) (f : ℕ → ℝ → ℝ)
    (hf1 : ∀ x, 0 ≤ x → f 1 x = x)
    (hfk : ∀ k, 1 ≤ k → k ≤ n →
      ContinuousOn (f k) (Set.Ici 0) ∧ MonotoneOn (f k) (Set.Ici 0) ∧ ∀ x, 0 ≤ x → 0 ≤ f k x)
    (hfdec : ∀ k, 1 ≤ k → k < n → ∀ x, 0 ≤ x → f (k + 1) x ≤ f k x)
    (hrule : ∀ l E, PrizeAlloc.Interval.IsRanking l → l.length ≤ n → 0 ≤ E →
      ∃ x, 0 ≤ x ∧ (∑ k ∈ Finset.Icc 1 l.length, f k x) = E ∧
        ∀ i ∈ l, φ l E i = f (PrizeAlloc.Interval.pos l i) x) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Set.Ici 0) ∧ MonotoneOn g (Set.Ici 0) ∧
      (∀ x, 0 ≤ x → 0 ≤ g x ∧ g x ≤ f n x) ∧
      ∀ l E, PrizeAlloc.Interval.IsRanking l → l.length = n + 1 → 0 ≤ E →
        ∃ x, 0 ≤ x ∧ (∑ k ∈ Finset.Icc 1 l.length, Function.update f (n + 1) g k x) = E ∧
          ∀ i ∈ l, φ l E i = Function.update f (n + 1) g (PrizeAlloc.Interval.pos l i) x := by
  classical
  -- Key consequence of top consistency and the induction hypothesis, for `|N| = n + 1`.
  have keyC : ∀ (l : List U) (E : ℝ), IsRanking l → l.length = n + 1 → 0 ≤ E →
      ∀ w ∈ l, pos l w = 1 → ∀ v ∈ l, pos l v = n + 1 →
      (∀ i ∈ l, pos l i ≤ n → φ l E i = f (pos l i) (φ l E w)) ∧
      (∀ i ∈ l, ¬ pos l i ≤ n → i = v) ∧
      E = ∑ k ∈ Finset.Icc 1 n, f k (φ l E w) + φ l E v := by
    intro l E hl hlen hE w hwl hwpos v hvl hvpos
    have hTlen : (l.take n).length = n := by simp [hlen]
    have hTr : IsRanking (l.take n) := by
      refine ⟨(List.take_sublist n l).nodup hl.1, ?_⟩
      intro h
      have := congrArg List.length h
      rw [hTlen] at this
      simp at this
      omega
    have hmemT : ∀ i ∈ l, (i ∈ l.take n ↔ pos l i ≤ n) := by
      intro i hi
      rw [List.mem_take_iff_idxOf_lt hi]
      unfold pos
      omega
    have hTsub : (l.take n).toFinset ⊆ l.toFinset := fun j hj =>
      List.mem_toFinset.mpr ((List.take_sublist n l).subset (List.mem_toFinset.mp hj))
    have hwT : w ∈ l.take n := (hmemT w hwl).mpr (by omega)
    have hTne : (l.take n).toFinset.Nonempty := ⟨w, List.mem_toFinset.mpr hwT⟩
    have hTcard : (l.take n).toFinset.card = n := by
      rw [List.toFinset_card_of_nodup hTr.1, hTlen]
    have hTC' := hTC l E hl hE (l.take n).toFinset hTsub hTne (fun i hi => by
      rw [hTcard]
      have hi' := List.mem_toFinset.mp hi
      exact (hmemT i ((List.take_sublist n l).subset hi')).mp hi')
    rw [sub_take l hl.1 n] at hTC'
    have hE' : 0 ≤ ∑ j ∈ (l.take n).toFinset, φ l E j :=
      Finset.sum_nonneg (fun j hj => (hφ l E hl hE).1 j (List.mem_toFinset.mp (hTsub hj)))
    obtain ⟨y, hy, -, hyφ⟩ := hrule (l.take n) _ hTr hTlen.le hE'
    have hyw : φ l E w = y := by
      rw [hTC' w (List.mem_toFinset.mpr hwT), hyφ w hwT, pos_take l n w hwT, hwpos, hf1 y hy]
    have ha : ∀ i ∈ l, pos l i ≤ n → φ l E i = f (pos l i) (φ l E w) := by
      intro i hi hin
      have hiT := (hmemT i hi).mpr hin
      rw [hTC' i (List.mem_toFinset.mpr hiT), hyφ i hiT, pos_take l n i hiT, hyw]
    have hb : ∀ i ∈ l, ¬ pos l i ≤ n → i = v := by
      intro i hi hin
      have h1 := List.idxOf_lt_length_of_mem hi
      have h2 : l.idxOf i = l.idxOf v := by unfold pos at hin hvpos; omega
      exact (List.idxOf_inj hi).mp h2
    refine ⟨ha, hb, ?_⟩
    have hsum := (hφ l E hl hE).2
    let G : ℕ → ℝ := fun k => if k ≤ n then f k (φ l E w) else φ l E v
    have hG : ∑ i ∈ l.toFinset, φ l E i = ∑ i ∈ l.toFinset, G (pos l i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := List.mem_toFinset.mp hi
      by_cases hin : pos l i ≤ n
      · simp only [G, if_pos hin]
        exact ha i hi' hin
      · simp only [G, if_neg hin]
        rw [hb i hi' hin]
    rw [hG, sum_pos_eq l hl.1 G, hlen, Finset.sum_Icc_succ_top (by omega)] at hsum
    have h1 : ∑ k ∈ Finset.Icc 1 n, G k = ∑ k ∈ Finset.Icc 1 n, f k (φ l E w) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [G, if_pos (Finset.mem_Icc.mp hk).2]
    have h2 : G (n + 1) = φ l E v := by simp only [G, if_neg (by omega : ¬ n + 1 ≤ n)]
    rw [h1, h2] at hsum
    exact hsum.symm
  by_cases h0 : ∃ l0 : List U, IsRanking l0 ∧ l0.length = n + 1
  swap
  · refine ⟨fun _ => 0, continuousOn_const, monotoneOn_const, ?_, ?_⟩
    · intro x hx
      exact ⟨le_rfl, (hfk n hn le_rfl).2.2 x hx⟩
    · intro l E hl hlen _
      exact absurd ⟨l, hl, hlen⟩ h0
  obtain ⟨l0, hl0, hl0len⟩ := h0
  have h0lt : 0 < l0.length := by omega
  have hnlt : n < l0.length := by omega
  have hn1lt : n - 1 < l0.length := by omega
  set w0 := l0[0] with hw0
  set v0 := l0[n] with hv0
  set u0 := l0[n - 1] with hu0
  have hw0m : w0 ∈ l0 := List.getElem_mem _
  have hv0m : v0 ∈ l0 := List.getElem_mem _
  have hu0m : u0 ∈ l0 := List.getElem_mem _
  have hw0p : pos l0 w0 = 1 := posGet l0 hl0.1 0 h0lt
  have hv0p : pos l0 v0 = n + 1 := posGet l0 hl0.1 n hnlt
  have hu0p : pos l0 u0 = n := by rw [hu0, posGet l0 hl0.1 (n - 1) hn1lt]; omega
  obtain ⟨hsm, -, -, hinv⟩ :=
    PrizeAlloc.Param.winner_prize_inverse φ hφ hOP hWSM hEC l0 hl0 w0 hw0m hw0p
  let h : ℝ → ℝ := fun E => φ l0 E w0
  let E0 : ℝ → ℝ := fun x => if 0 ≤ x then Function.invFunOn h (Set.Ici 0) x else x
  have hE0 : ∀ x, 0 ≤ x → 0 ≤ E0 x ∧ φ l0 (E0 x) w0 = x := by
    intro x hx
    obtain ⟨E, ⟨hE, hEx⟩, -⟩ := hinv x hx
    have := Function.invFunOn_pos (f := h) (s := Set.Ici 0) (b := x) ⟨E, Set.mem_Ici.mpr hE, hEx⟩
    simp only [E0, if_pos hx]
    exact ⟨this.1, this.2⟩
  have hhnn : ∀ E, 0 ≤ E → 0 ≤ φ l0 E w0 := fun E hE => (hφ l0 E hl0 hE).1 w0 hw0m
  have hE0inv : ∀ E, 0 ≤ E → E0 (φ l0 E w0) = E := by
    intro E hE
    have := hE0 (φ l0 E w0) (hhnn E hE)
    exact hsm.injOn (Set.mem_Ici.mpr this.1) (Set.mem_Ici.mpr hE) this.2
  have hE0mono : Monotone E0 := by
    intro x y hxy
    by_cases hx : 0 ≤ x
    · have hy : 0 ≤ y := hx.trans hxy
      by_contra hc
      push Not at hc
      have := hsm (Set.mem_Ici.mpr (hE0 y hy).1) (Set.mem_Ici.mpr (hE0 x hx).1) hc
      simp only at this
      rw [(hE0 x hx).2, (hE0 y hy).2] at this
      linarith
    · by_cases hy : 0 ≤ y
      · have h1 : E0 x = x := by simp only [E0, if_neg hx]
        rw [h1]
        linarith [(hE0 y hy).1]
      · simp only [E0, if_neg hx, if_neg hy]
        exact hxy
  have hE0surj : Function.Surjective E0 := by
    intro E
    by_cases hE : 0 ≤ E
    · exact ⟨φ l0 E w0, hE0inv E hE⟩
    · exact ⟨E, by simp only [E0, if_neg hE]⟩
  have hE0cont : Continuous E0 := hE0mono.continuous_of_surjective hE0surj
  let g : ℝ → ℝ := fun x => φ l0 (E0 x) v0
  -- the formula `g x = E0 x - ∑_{k ≤ n} f k x`
  have hgform : ∀ x, 0 ≤ x → g x = E0 x - ∑ k ∈ Finset.Icc 1 n, f k x := by
    intro x hx
    obtain ⟨-, -, hc⟩ := keyC l0 (E0 x) hl0 hl0len (hE0 x hx).1 w0 hw0m hw0p v0 hv0m hv0p
    rw [(hE0 x hx).2] at hc
    simp only [g]
    linarith
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · -- continuity
    have hc : ContinuousOn (fun x => E0 x - ∑ k ∈ Finset.Icc 1 n, f k x) (Set.Ici 0) := by
      apply hE0cont.continuousOn.sub
      apply continuousOn_finsetSum
      intro k hk
      exact (hfk k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2).1
    exact hc.congr (fun x hx => hgform x hx)
  · -- monotonicity
    intro x hx y hy hxy
    have hle := hE0mono hxy
    rcases hle.lt_or_eq with hlt | heq
    · exact hWSM.1 l0 (E0 x) (E0 y) hl0 (hE0 x hx).1 hlt v0 hv0m
    · simp only [g]
      rw [heq]
  · intro x hx
    refine ⟨(hφ l0 (E0 x) hl0 (hE0 x hx).1).1 v0 hv0m, ?_⟩
    obtain ⟨ha, -, -⟩ := keyC l0 (E0 x) hl0 hl0len (hE0 x hx).1 w0 hw0m hw0p v0 hv0m hv0p
    have h1 := hOP l0 (E0 x) hl0 (hE0 x hx).1 u0 hu0m v0 hv0m (by omega)
    rw [ha u0 hu0m (by omega), hu0p, (hE0 x hx).2] at h1
    exact h1
  · intro l E hl hlen hE
    have h0l : 0 < l.length := by omega
    have hnl : n < l.length := by omega
    have hwm : l[0] ∈ l := List.getElem_mem _
    have hvm : l[n] ∈ l := List.getElem_mem _
    have hwp : pos l l[0] = 1 := posGet l hl.1 0 h0l
    have hvp : pos l l[n] = n + 1 := posGet l hl.1 n hnl
    obtain ⟨ha, hb, hc⟩ := keyC l E hl hlen hE l[0] hwm hwp l[n] hvm hvp
    have hlen' : l.length = l0.length := by omega
    have hAw : φ l E l[0] = φ l0 E w0 := hA l l0 E hl hl0 hE hlen' _ hwm _ hw0m (by rw [hwp, hw0p])
    have hAv : φ l E l[n] = φ l0 E v0 := hA l l0 E hl hl0 hE hlen' _ hvm _ hv0m (by rw [hvp, hv0p])
    have hgx : g (φ l E l[0]) = φ l E l[n] := by
      simp only [g]
      rw [hAw, hE0inv E hE, hAv]
    refine ⟨φ l E l[0], (hφ l E hl hE).1 _ hwm, ?_, ?_⟩
    · rw [hlen, Finset.sum_Icc_succ_top (by omega), Function.update_self, hgx]
      have h1 : ∑ k ∈ Finset.Icc 1 n, Function.update f (n + 1) g k (φ l E l[0])
          = ∑ k ∈ Finset.Icc 1 n, f k (φ l E l[0]) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Function.update_of_ne (by have := (Finset.mem_Icc.mp hk).2; omega)]
      rw [h1]
      exact hc.symm
    · intro i hi
      by_cases hin : pos l i ≤ n
      · rw [Function.update_of_ne (by omega), ha i hi hin]
      · rw [hb i hi hin, hvp, Function.update_self, hgx]
