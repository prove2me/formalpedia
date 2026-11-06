-- Prove2me | solution 1 for ReliableFacilityLoc.Supermod.bracket_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T00:07:11.561135+00:00
-- url     : https://prove2.me/submissions/b8da08c2-33e6-4fe2-ba94-a85a59b6ef4d

import Mathlib
import Definitions.Def_ReliableFacilityLoc_Supermod_RSP
import Definitions.Def_ReliableFacilityLoc_Supermod_ClosedForm
import Theorems.Thm_ReliableFacilityLoc_Supermod_closed_form

open Finset


namespace RFL3Aux
open ReliableFacilityLoc.Supermod

variable {J : ℕ}

noncomputable def hv (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) : List (Fin J) → ℝ
  | [] => phi
  | x :: xs => if d x ≤ phi then (1 - q x) * d x + q x * hv d phi q xs else phi

noncomputable def fv (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) : List (Fin J) → ℝ
  | [] => phi
  | x :: xs => (1 - q x) * d x + q x * fv d phi q xs

section
variable (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)

lemma hv_le (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) : ∀ L : List (Fin J), hv d phi q L ≤ phi
  | [] => le_rfl
  | x :: xs => by
    simp only [hv]
    split_ifs with h
    · have h1 : (1 - q x) * d x ≤ (1 - q x) * phi :=
        mul_le_mul_of_nonneg_left h (by linarith [hq1 x])
      have h2 := mul_le_mul_of_nonneg_left (hv_le hq0 hq1 xs) (hq0 x)
      nlinarith
    · exact le_rfl

lemma hv_all_gt : ∀ L : List (Fin J), (∀ y ∈ L, phi < d y) → hv d phi q L = phi
  | [] => fun _ => rfl
  | x :: xs => fun h => by
    simp only [hv]
    rw [if_neg (not_le.mpr (h x (by simp)))]

lemma hv_erase (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) : ∀ (L : List (Fin J)),
    L.Pairwise (fun a b => d a ≤ d b) → ∀ a ∈ L,
    hv d phi q L ≤ (1 - q a) * d a + q a * hv d phi q (L.erase a)
  | [], _, a, ha => absurd ha List.not_mem_nil
  | y :: ys, hs, a, ha => by
    rw [List.pairwise_cons] at hs
    by_cases hya : y = a
    · subst hya
      rw [List.erase_cons_head]
      simp only [hv]
      split_ifs with h
      · exact le_rfl
      · have hall : ∀ z ∈ ys, phi < d z := fun z hz => lt_of_lt_of_le (not_le.mp h) (hs.1 z hz)
        rw [hv_all_gt d phi q ys hall]
        have := hq1 y
        nlinarith [not_le.mp h]
    · have ha' : a ∈ ys := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h.symm hya
        · exact h
      rw [List.erase_cons_tail (by simpa using hya)]
      have hya' : d y ≤ d a := hs.1 a ha'
      simp only [hv]
      split_ifs with h
      · have ih := hv_erase hq0 hq1 ys hs.2 a ha'
        have h1 := mul_le_mul_of_nonneg_left ih (hq0 y)
        have h2 : 0 ≤ (1 - q a) * (1 - q y) * (d a - d y) := by
          apply mul_nonneg (mul_nonneg _ _) <;> linarith [hq1 a, hq1 y]
        nlinarith
      · have := hq1 a
        have : phi < d a := lt_of_lt_of_le (not_le.mp h) hya'
        nlinarith

lemma hv_eq_fv : ∀ L : List (Fin J),
    hv d phi q L = fv d phi q (L.takeWhile (fun j => decide (d j ≤ phi)))
  | [] => rfl
  | x :: xs => by
    rw [List.takeWhile_cons]
    by_cases h : d x ≤ phi
    · simp only [h, decide_true, if_true, hv, fv, hv_eq_fv xs]
    · simp [h, hv, fv]

lemma prodQ_zero (L : List (Fin J)) : prodQ q L 0 = 1 := by simp [prodQ]

lemma prodQ_cons_succ (x : Fin J) (L : List (Fin J)) (k : ℕ) :
    prodQ q (x :: L) (k + 1) = q x * prodQ q L k := by simp [prodQ]

lemma prodQ_succ (L : List (Fin J)) (n : ℕ) (hn : n < L.length) :
    prodQ q L (n + 1) = prodQ q L n * q L[n] := by
  unfold prodQ
  rw [List.take_add_one, List.getElem?_eq_getElem hn, List.map_append, List.prod_append]
  simp

lemma prod_map_mem01 (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) :
    ∀ l : List (Fin J), 0 ≤ (l.map q).prod ∧ (l.map q).prod ≤ 1
  | [] => by simp
  | x :: xs => by
    obtain ⟨h1, h2⟩ := prod_map_mem01 hq0 hq1 xs
    simp only [List.map_cons, List.prod_cons]
    exact ⟨mul_nonneg (hq0 x) h1, mul_le_one₀ (hq1 x).le h1 h2⟩

lemma prodQ_mem01 (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (L : List (Fin J)) (n : ℕ) :
    0 ≤ prodQ q L n ∧ prodQ q L n ≤ 1 := prod_map_mem01 q hq0 hq1 _

lemma sum_Icc_shift (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Icc 1 (n + 1), f k = ∑ i ∈ range (n + 1), f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ _ (n + 1)]

lemma Ck_cons_one (x : Fin J) (xs : List (Fin J)) (h : d x ≤ phi) :
    Ck d phi q (x :: xs) 1 = (1 - q x) * d x := by
  have hc : countLE d phi (x :: xs) = countLE d phi xs + 1 := by
    unfold countLE; exact List.countP_cons_of_pos (by simpa using h)
  unfold Ck
  rw [hc, if_neg (by omega), if_pos (by omega)]
  simp [prodQ_zero]

lemma Ck_cons_succ (x : Fin J) (xs : List (Fin J)) (h : d x ≤ phi) (k : ℕ) (hk : 1 ≤ k) :
    Ck d phi q (x :: xs) (k + 1) = q x * Ck d phi q xs k := by
  have hc : countLE d phi (x :: xs) = countLE d phi xs + 1 := by
    unfold countLE; exact List.countP_cons_of_pos (by simpa using h)
  unfold Ck
  rw [hc]
  by_cases h1 : k = countLE d phi xs + 1
  · rw [if_pos (by omega), if_pos h1, prodQ_cons_succ]; ring
  · rw [if_neg (by omega), if_neg h1]
    by_cases h2 : 1 ≤ k ∧ k ≤ countLE d phi xs
    · rw [if_pos (by omega), if_pos h2]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel, prodQ_cons_succ, List.map_cons]
      simp [List.getD_cons_succ]
      ring
    · rw [if_neg (by omega), if_neg h2, mul_zero]

lemma sumCk_eq : ∀ L : List (Fin J), L.Pairwise (fun a b => d a ≤ d b) →
    ∑ k ∈ Icc 1 (countLE d phi L + 1), Ck d phi q L k = hv d phi q L
  | [], _ => by
    simp [countLE, Ck, prodQ, hv]
  | x :: xs, hs => by
    rw [List.pairwise_cons] at hs
    by_cases h : d x ≤ phi
    · have hc : countLE d phi (x :: xs) = countLE d phi xs + 1 := by
        unfold countLE; exact List.countP_cons_of_pos (by simpa using h)
      rw [hc, sum_Icc_shift, sum_range_succ']
      simp only [hv, if_pos h]
      rw [Ck_cons_one d phi q x xs h]
      have : ∀ i ∈ range (countLE d phi xs + 1), Ck d phi q (x :: xs) (i + 1 + 1) =
          q x * Ck d phi q xs (i + 1) := fun i _ => Ck_cons_succ d phi q x xs h (i + 1) (by omega)
      rw [sum_congr rfl this, ← mul_sum, ← sum_Icc_shift, sumCk_eq xs hs.2]
      ring
    · have hall : ∀ z ∈ x :: xs, phi < d z := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact not_le.mp h
        · exact lt_of_lt_of_le (not_le.mp h) (hs.1 z hz)
      have hc : countLE d phi (x :: xs) = 0 := by
        unfold countLE
        rw [List.countP_eq_zero]
        intro a ha; simpa using hall a ha
      rw [hc, hv_all_gt d phi q _ hall]
      simp [Ck, hc, prodQ_zero]

lemma fv_sum : ∀ M : List (Fin J),
    fv d phi q M = ∑ n ∈ range M.length, prodQ q M n * (M.map (fun j => (1 - q j) * d j)).getD n 0
      + prodQ q M M.length * phi
  | [] => by simp [fv, prodQ]
  | x :: xs => by
    rw [List.length_cons, sum_range_succ', fv, fv_sum xs]
    simp only [prodQ_cons_succ, prodQ_zero, List.map_cons, List.getD_cons_succ,
      List.getD_cons_zero]
    rw [mul_add, mul_sum]
    have : ∀ i ∈ range xs.length, q x * (prodQ q xs i *
        (List.map (fun j => (1 - q j) * d j) xs).getD i 0) =
        q x * prodQ q xs i * (List.map (fun j => (1 - q j) * d j) xs).getD i 0 :=
      fun i _ => by ring
    rw [sum_congr rfl this]
    ring

end


section
variable (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)

/-- one step of the recursion -/
noncomputable def gs (x : Fin J) (w : ℝ) : ℝ := if d x ≤ phi then (1 - q x) * d x + q x * w else phi

lemma hv_cons_eq (x : Fin J) (xs : List (Fin J)) : hv d phi q (x :: xs) = gs d phi q x (hv d phi q xs) :=
  rfl

lemma gs_mono (hq0 : ∀ j, 0 ≤ q j) (x : Fin J) {a b : ℝ} (h : a ≤ b) :
    gs d phi q x a ≤ gs d phi q x b := by
  unfold gs; split_ifs
  · have := mul_le_mul_of_nonneg_left h (hq0 x); linarith
  · exact le_rfl

/-- `X ≤ Y → g_a X + Y ≥ g_a Y + X` -/
lemma gs_K (hq1 : ∀ j, q j < 1) (a : Fin J) {X Y : ℝ} (h : X ≤ Y) :
    gs d phi q a Y + X ≤ gs d phi q a X + Y := by
  unfold gs; split_ifs
  · have : q a * (Y - X) ≤ 1 * (Y - X) := mul_le_mul_of_nonneg_right (hq1 a).le (by linarith)
    linarith
  · linarith

lemma gs_lin (hq0 : ∀ j, 0 ≤ q j) (x : Fin J) {A B C D : ℝ} (h : C + D ≤ A + B) :
    gs d phi q x C + gs d phi q x D ≤ gs d phi q x A + gs d phi q x B := by
  unfold gs; split_ifs
  · have := mul_le_mul_of_nonneg_left h (hq0 x); linarith
  · linarith

lemma hv_ge (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (c : ℝ) (hc : c ≤ phi) :
    ∀ L : List (Fin J), (∀ y ∈ L, c ≤ d y) → c ≤ hv d phi q L
  | [], _ => hc
  | x :: xs, h => by
    simp only [hv]
    split_ifs with hx
    · have h1 := hv_ge hq0 hq1 c hc xs (fun y hy => h y (by simp [hy]))
      have h2 := h x (by simp)
      have e1 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 - q x by linarith [hq1 x])
      have e2 := mul_le_mul_of_nonneg_left h1 (hq0 x)
      nlinarith
    · exact hc

/-- Lemma A: `g_v (h L) ≤ h L` when `v` is not farther than any entry of `L`. -/
lemma gs_le_hv (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (v : Fin J) (L : List (Fin J))
    (h : ∀ y ∈ L, d v ≤ d y) : gs d phi q v (hv d phi q L) ≤ hv d phi q L := by
  unfold gs
  split_ifs with hv'
  · have := hv_ge d phi q hq0 hq1 (d v) hv' L h
    have e := mul_le_mul_of_nonneg_left this (show 0 ≤ 1 - q v by linarith [hq1 v])
    nlinarith
  · rw [hv_all_gt d phi q L (fun y hy => lt_of_lt_of_le (not_le.mp hv') (h y hy))]

lemma hv_ins_le (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (v : Fin J) :
    ∀ L : List (Fin J), L.Pairwise (fun a b => d a ≤ d b) →
    hv d phi q (L.orderedInsert (fun a b => d a ≤ d b) v) ≤ hv d phi q L
  | [], _ => by
    simp only [List.orderedInsert_nil]
    exact gs_le_hv d phi q hq0 hq1 v [] (by simp)
  | x :: xs, hs => by
    rw [List.pairwise_cons] at hs
    rw [List.orderedInsert_cons]
    split_ifs with hvx
    · rw [hv_cons_eq]
      apply gs_le_hv d phi q hq0 hq1 v
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hvx
      · exact le_trans hvx (hs.1 y hy)
    · rw [hv_cons_eq, hv_cons_eq]
      exact gs_mono d phi q hq0 x (hv_ins_le hq0 hq1 v xs hs.2)

lemma head_case (hq1 : ∀ j, q j < 1) (hq0 : ∀ j, 0 ≤ q j) (u v : Fin J) (L : List (Fin J))
    (hu : ∀ y ∈ L, d u ≤ d y) (hv' : ∀ y ∈ L, d v ≤ d y) :
    hv d phi q (u :: L) + hv d phi q (v :: L) ≤
      hv d phi q ((v :: L).orderedInsert (fun a b => d a ≤ d b) u) + hv d phi q L := by
  rw [List.orderedInsert_cons]
  split_ifs with huv
  · have hX := gs_le_hv d phi q hq0 hq1 v L hv'
    have := gs_K d phi q hq1 u hX
    simp only [hv_cons_eq]
    linarith
  · have hu' : ∀ y ∈ L, ¬ d u ≤ d y → False := fun y hy h => h (hu y hy)
    have hins : L.orderedInsert (fun a b => d a ≤ d b) u = u :: L := by
      cases L with
      | nil => rfl
      | cons y ys => rw [List.orderedInsert_cons, if_pos (hu y (by simp))]
    rw [hins]
    have hX := gs_le_hv d phi q hq0 hq1 u L hu
    have := gs_K d phi q hq1 v hX
    simp only [hv_cons_eq]
    linarith

lemma hv_supermod (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (u v : Fin J) :
    ∀ L : List (Fin J), L.Pairwise (fun a b => d a ≤ d b) →
    hv d phi q (L.orderedInsert (fun a b => d a ≤ d b) u) +
      hv d phi q (L.orderedInsert (fun a b => d a ≤ d b) v) ≤
    hv d phi q ((L.orderedInsert (fun a b => d a ≤ d b) v).orderedInsert
      (fun a b => d a ≤ d b) u) + hv d phi q L
  | [], _ => by
    simp only [List.orderedInsert_nil]
    exact head_case d phi q hq1 hq0 u v [] (by simp) (by simp)
  | x :: xs, hs => by
    have hs' := hs
    rw [List.pairwise_cons] at hs'
    by_cases hux : d u ≤ d x <;> by_cases hvx : d v ≤ d x
    · have e1 : (x :: xs).orderedInsert (fun a b => d a ≤ d b) u = u :: x :: xs := by
        rw [List.orderedInsert_cons, if_pos hux]
      have e2 : (x :: xs).orderedInsert (fun a b => d a ≤ d b) v = v :: x :: xs := by
        rw [List.orderedInsert_cons, if_pos hvx]
      rw [e1, e2]
      have hall : ∀ c, c ≤ d x → ∀ y ∈ x :: xs, c ≤ d y := by
        intro c hc y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hc
        · exact le_trans hc (hs'.1 y hy)
      exact head_case d phi q hq1 hq0 u v (x :: xs) (hall _ hux) (hall _ hvx)
    · -- du ≤ dx < dv
      have e1 : (x :: xs).orderedInsert (fun a b => d a ≤ d b) u = u :: x :: xs := by
        rw [List.orderedInsert_cons, if_pos hux]
      have e2 : (x :: xs).orderedInsert (fun a b => d a ≤ d b) v =
          x :: xs.orderedInsert (fun a b => d a ≤ d b) v := by
        rw [List.orderedInsert_cons, if_neg hvx]
      have e3 : (x :: xs.orderedInsert (fun a b => d a ≤ d b) v).orderedInsert
          (fun a b => d a ≤ d b) u = u :: x :: xs.orderedInsert (fun a b => d a ≤ d b) v := by
        rw [List.orderedInsert_cons, if_pos hux]
      rw [e1, e2, e3]
      simp only [hv_cons_eq]
      have hX := gs_mono d phi q hq0 x (hv_ins_le d phi q hq0 hq1 v xs hs'.2)
      have := gs_K d phi q hq1 u hX
      linarith
    · -- dv ≤ dx < du
      have e1 : (x :: xs).orderedInsert (fun a b => d a ≤ d b) u =
          x :: xs.orderedInsert (fun a b => d a ≤ d b) u := by
        rw [List.orderedInsert_cons, if_neg hux]
      have e2 : (x :: xs).orderedInsert (fun a b => d a ≤ d b) v = v :: x :: xs := by
        rw [List.orderedInsert_cons, if_pos hvx]
      have e3 : (v :: x :: xs).orderedInsert (fun a b => d a ≤ d b) u =
          v :: x :: xs.orderedInsert (fun a b => d a ≤ d b) u := by
        rw [List.orderedInsert_cons, if_neg (fun h => hux (le_trans h hvx)), e1]
      rw [e1, e2, e3]
      simp only [hv_cons_eq]
      have hX := gs_mono d phi q hq0 x (hv_ins_le d phi q hq0 hq1 u xs hs'.2)
      have := gs_K d phi q hq1 v hX
      linarith
    · -- dx < du, dx < dv
      have e1 : (x :: xs).orderedInsert (fun a b => d a ≤ d b) u =
          x :: xs.orderedInsert (fun a b => d a ≤ d b) u := by
        rw [List.orderedInsert_cons, if_neg hux]
      have e2 : (x :: xs).orderedInsert (fun a b => d a ≤ d b) v =
          x :: xs.orderedInsert (fun a b => d a ≤ d b) v := by
        rw [List.orderedInsert_cons, if_neg hvx]
      have e3 : (x :: xs.orderedInsert (fun a b => d a ≤ d b) v).orderedInsert
          (fun a b => d a ≤ d b) u = x :: (xs.orderedInsert (fun a b => d a ≤ d b) v).orderedInsert
            (fun a b => d a ≤ d b) u := by
        rw [List.orderedInsert_cons, if_neg hux]
      rw [e1, e2, e3]
      simp only [hv_cons_eq]
      exact gs_lin d phi q hq0 x (hv_supermod hq0 hq1 u v xs hs'.2)

end

lemma ins_props (d : Fin J → ℝ) (a : Fin J) (L : List (Fin J)) (T : Finset (Fin J))
    (hLnd : L.Nodup) (hLT : L.toFinset = T) (ha : a ∉ T)
    (hs : L.Pairwise (fun a b => d a ≤ d b)) :
    (L.orderedInsert (fun a b => d a ≤ d b) a).Nodup ∧
    (L.orderedInsert (fun a b => d a ≤ d b) a).toFinset = insert a T ∧
    (L.orderedInsert (fun a b => d a ≤ d b) a).Pairwise (fun a b => d a ≤ d b) := by
  have hp := List.perm_orderedInsert (fun a b => d a ≤ d b) a L
  have haL : a ∉ L := fun h => ha (by rw [← hLT]; exact List.mem_toFinset.mpr h)
  refine ⟨hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨haL, hLnd⟩), ?_, ?_⟩
  · rw [List.toFinset_eq_of_perm _ _ hp, List.toFinset_cons, hLT]
  · haveI : Std.Total (fun a b : Fin J => d a ≤ d b) := ⟨fun a b => le_total _ _⟩
    haveI : IsTrans (Fin J) (fun a b => d a ≤ d b) := ⟨fun a b c => le_trans⟩
    exact hs.orderedInsert a L

end RFL3Aux



namespace RFL3Aux
open ReliableFacilityLoc.Supermod

variable {J : ℕ}

section
variable (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)

lemma countLE_cons_pos (c : ℝ) (x : Fin J) (xs : List (Fin J)) (h : d x ≤ c) :
    countLE d c (x :: xs) = countLE d c xs + 1 := by
  unfold countLE; exact List.countP_cons_of_pos (by simpa using h)

lemma countLE_eq_zero (c : ℝ) (L : List (Fin J)) (h : ∀ y ∈ L, c < d y) : countLE d c L = 0 := by
  unfold countLE; rw [List.countP_eq_zero]; intro a ha; simpa using h a ha

lemma countLE_mono {c c' : ℝ} (h : c ≤ c') (L : List (Fin J)) :
    countLE d c L ≤ countLE d c' L :=
  List.countP_mono_left (fun x _ hx => by simp only [decide_eq_true_eq] at hx ⊢; linarith)

lemma split_props (c : ℝ) : ∀ L : List (Fin J), L.Pairwise (fun a b => d a ≤ d b) →
    (∀ y ∈ L.take (countLE d c L), d y ≤ c) ∧ (∀ y ∈ L.drop (countLE d c L), c < d y)
  | [], _ => by simp
  | x :: xs, hs => by
    rw [List.pairwise_cons] at hs
    by_cases hx : d x ≤ c
    · rw [countLE_cons_pos d c x xs hx, List.take_succ_cons, List.drop_succ_cons]
      obtain ⟨h1, h2⟩ := split_props c xs hs.2
      refine ⟨fun y hy => ?_, h2⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact h1 y hy
    · have hall : ∀ y ∈ x :: xs, c < d y := by
        intro y hy; rcases List.mem_cons.mp hy with rfl | hy
        · exact not_le.mp hx
        · exact lt_of_lt_of_le (not_le.mp hx) (hs.1 y hy)
      rw [countLE_eq_zero d c _ hall]
      simpa using hall

lemma sum_Icc_succ_shift (f : ℕ → ℝ) (a b : ℕ) :
    ∑ k ∈ Icc (a + 1) (b + 1), f k = ∑ k ∈ Icc a b, f (k + 1) := by
  rw [← Finset.map_add_right_Icc a b 1, Finset.sum_map]; rfl

lemma sumCk_tail : ∀ (L : List (Fin J)) (t : ℕ), L.Pairwise (fun a b => d a ≤ d b) →
    t ≤ countLE d phi L →
    ∑ k ∈ Icc (t + 1) (countLE d phi L + 1), Ck d phi q L k = prodQ q L t * hv d phi q (L.drop t)
  | L, 0, hs, _ => by rw [sumCk_eq d phi q L hs, prodQ_zero]; simp
  | [], t + 1, _, ht => by simp [countLE] at ht
  | x :: xs, t + 1, hs, ht => by
    have hs' := List.pairwise_cons.mp hs
    have hx : d x ≤ phi := by
      by_contra hx
      have hall : ∀ y ∈ x :: xs, phi < d y := by
        intro y hy; rcases List.mem_cons.mp hy with rfl | hy
        · exact not_le.mp hx
        · exact lt_of_lt_of_le (not_le.mp hx) (hs'.1 y hy)
      rw [countLE_eq_zero d phi _ hall] at ht; omega
    rw [countLE_cons_pos d phi x xs hx] at ht ⊢
    rw [sum_Icc_succ_shift]
    have : ∀ k ∈ Icc (t + 1) (countLE d phi xs + 1), Ck d phi q (x :: xs) (k + 1) =
        q x * Ck d phi q xs k := fun k hk =>
      Ck_cons_succ d phi q x xs hx k (by simp only [mem_Icc] at hk; omega)
    rw [sum_congr rfl this, ← mul_sum, sumCk_tail xs t hs'.2 (by omega), prodQ_cons_succ,
      List.drop_succ_cons]
    ring

lemma sum_Icc_split (f : ℕ → ℝ) {t s n : ℕ} (h1 : t ≤ s) (h2 : s ≤ n) :
    ∑ k ∈ Icc (t + 1) n, f k = ∑ k ∈ Icc (t + 1) s, f k + ∑ k ∈ Icc (s + 1) n, f k := by
  have e : ∀ a b : ℕ, Icc (a + 1) b = Ioc a b := fun a b => by ext; simp
  rw [e, e, e, Finset.sum_Ioc_consecutive f h1 h2]

lemma hv_append_diff (B B' : List (Fin J)) : ∀ A : List (Fin J), (∀ y ∈ A, d y ≤ phi) →
    hv d phi q (A ++ B) - hv d phi q (A ++ B') = (A.map q).prod * (hv d phi q B - hv d phi q B')
  | [], _ => by simp
  | x :: xs, h => by
    simp only [List.cons_append, hv, if_pos (h x (by simp)), List.map_cons, List.prod_cons]
    have := hv_append_diff B B' xs (fun y hy => h y (by simp [hy]))
    linear_combination q x * this

lemma hv_insert_mid (A B : List (Fin J)) (a : Fin J) (hA : ∀ y ∈ A, d y ≤ phi)
    (ha : d a ≤ phi) :
    hv d phi q (A ++ a :: B) - hv d phi q (A ++ B) =
      (A.map q).prod * ((1 - q a) * (d a - hv d phi q B)) := by
  rw [hv_append_diff d phi q (a :: B) B A hA]; simp only [hv, if_pos ha]; ring

lemma hv_ins_far (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (v : Fin J) (hv' : phi ≤ d v) :
    ∀ L : List (Fin J), L.Pairwise (fun a b => d a ≤ d b) →
    hv d phi q (L.orderedInsert (fun a b => d a ≤ d b) v) = hv d phi q L
  | [], _ => by
    simp only [List.orderedInsert_nil, hv]
    split_ifs with h
    · have : d v = phi := le_antisymm h hv'
      rw [this]; ring
    · rfl
  | x :: xs, hs => by
    rw [List.pairwise_cons] at hs
    rw [List.orderedInsert_cons]
    split_ifs with hvx
    · have hall : ∀ y ∈ x :: xs, phi ≤ d y := by
        intro y hy; rcases List.mem_cons.mp hy with rfl | hy
        · exact le_trans hv' hvx
        · exact le_trans hv' (le_trans hvx (hs.1 y hy))
      have hL : hv d phi q (x :: xs) = phi :=
        le_antisymm (hv_le d phi q hq0 hq1 _) (hv_ge d phi q hq0 hq1 phi le_rfl _ hall)
      rw [hv_cons_eq, hL]
      unfold gs
      split_ifs with h
      · have : d v = phi := le_antisymm h hv'
        rw [this]; ring
      · rfl
    · rw [hv_cons_eq, hv_cons_eq, hv_ins_far hq0 hq1 v hv' xs hs.2]

end

lemma mid_props (d : Fin J → ℝ) (A B : List (Fin J)) (a : Fin J) (T : Finset (Fin J))
    (hnd : (A ++ B).Nodup) (hT : (A ++ B).toFinset = T) (ha : a ∉ T)
    (hs : (A ++ B).Pairwise (fun a b => d a ≤ d b)) (hA : ∀ y ∈ A, d y ≤ d a)
    (hB : ∀ y ∈ B, d a ≤ d y) :
    (A ++ a :: B).Nodup ∧ (A ++ a :: B).toFinset = insert a T ∧
    (A ++ a :: B).Pairwise (fun a b => d a ≤ d b) := by
  have hp : (A ++ a :: B).Perm (a :: (A ++ B)) := List.perm_middle
  have haL : a ∉ A ++ B := fun h => ha (by rw [← hT]; exact List.mem_toFinset.mpr h)
  refine ⟨hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨haL, hnd⟩), ?_, ?_⟩
  · rw [List.toFinset_eq_of_perm _ _ hp, List.toFinset_cons, hT]
  · rw [List.pairwise_append] at hs ⊢
    refine ⟨hs.1, List.pairwise_cons.mpr ⟨hB, hs.2.1⟩, fun x hx y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hA x hx
    · exact hs.2.2 x hx y hy

lemma cf_hv {R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (hlam : 0 ≤ lam) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (hR : 1 ≤ R)
    (T : Finset (Fin J)) (M : List (Fin J)) (hT : T.card ≤ R) (hMnd : M.Nodup)
    (hMT : M.toFinset = T) (hMs : M.Pairwise (fun a b => d a ≤ d b)) :
    Phi lam d phi q mu R T = lam * hv d phi q M + ∑ j ∈ T, mu j := by
  rw [closed_form lam d phi q mu hlam hq0 hq1 hR T hT M hMnd hMT hMs, sumCk_eq d phi q M hMs]

theorem bracket_sol (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (L : List (Fin J))
    (hLsort : L.Pairwise (fun a b => d a ≤ d b)) (v : Fin J) (hv' : d v ≤ phi) :
    prodQ q L (countLE d (d v) L) * d v -
      ∑ k ∈ Icc (countLE d (d v) L + 1) (countLE d phi L + 1), Ck d phi q L k ≤ 0 := by
  rw [sumCk_tail d phi q L _ hLsort (countLE_mono d hv' L)]
  have h1 := (split_props d (d v) L hLsort).2
  have h2 := hv_ge d phi q hq0 hq1 (d v) hv' _ (fun y hy => (h1 y hy).le)
  have h3 := (prodQ_mem01 q hq0 hq1 L (countLE d (d v) L)).1
  have := mul_le_mul_of_nonneg_left h2 h3
  linarith

end RFL3Aux



namespace RFL3Aux
open ReliableFacilityLoc.Supermod

variable {J : ℕ}

theorem marginal_sol {R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (hlam : 0 ≤ lam) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (hR : 1 ≤ R)
    (S : Finset (Fin J)) (v : Fin J) (hv : v ∉ S) (hS : S.card + 1 ≤ R) (L : List (Fin J))
    (hLnd : L.Nodup) (hLS : L.toFinset = S) (hLsort : L.Pairwise (fun a b => d a ≤ d b)) :
    (d v ≤ phi →
      Phi lam d phi q mu R (insert v S) - Phi lam d phi q mu R S =
        lam * (1 - q v) * (prodQ q L (countLE d (d v) L) * d v -
          ∑ k ∈ Icc (countLE d (d v) L + 1) (countLE d phi L + 1), Ck d phi q L k) + mu v) ∧
    (phi ≤ d v →
      Phi lam d phi q mu R (insert v S) - Phi lam d phi q mu R S = mu v) := by
  have c1 : (insert v S).card ≤ R := by have := card_insert_le v S; omega
  have hS0 : S.card ≤ R := by omega
  constructor
  · intro hdv
    set t := countLE d (d v) L
    have hsp := split_props d (d v) L hLsort
    have hL : L.take t ++ L.drop t = L := List.take_append_drop t L
    obtain ⟨h1, h2, h3⟩ := mid_props d (L.take t) (L.drop t) v S (by rw [hL]; exact hLnd)
      (by rw [hL]; exact hLS) hv (by rw [hL]; exact hLsort) hsp.1 (fun y hy => (hsp.2 y hy).le)
    rw [cf_hv lam d phi q mu hlam hq0 hq1 hR _ _ c1 h1 h2 h3,
      cf_hv lam d phi q mu hlam hq0 hq1 hR _ _ hS0 hLnd hLS hLsort, sum_insert hv,
      sumCk_tail d phi q L t hLsort (countLE_mono d hdv L)]
    have hdiff := hv_insert_mid d phi q (L.take t) (L.drop t) v
      (fun y hy => le_trans (hsp.1 y hy) hdv) hdv
    rw [hL] at hdiff
    have e : ((L.take t).map q).prod = prodQ q L t := rfl
    rw [e] at hdiff
    linear_combination lam * hdiff
  · intro hdv
    obtain ⟨h1, h2, h3⟩ := ins_props d v L S hLnd hLS hv hLsort
    rw [cf_hv lam d phi q mu hlam hq0 hq1 hR _ _ c1 h1 h2 h3,
      cf_hv lam d phi q mu hlam hq0 hq1 hR _ _ hS0 hLnd hLS hLsort, sum_insert hv,
      hv_ins_far d phi q hq0 hq1 v hdv L hLsort]
    ring

theorem case1_sol {R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (hlam : 0 ≤ lam) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (hR : 1 ≤ R)
    (S : Finset (Fin J)) (u v : Fin J) (huv : u ≠ v) (hu : u ∉ S) (hv : v ∉ S)
    (hS : S.card + 2 ≤ R) (L : List (Fin J)) (hLnd : L.Nodup) (hLS : L.toFinset = S)
    (hLsort : L.Pairwise (fun a b => d a ≤ d b)) (hduv : d u ≤ d v) (hdv : d v ≤ phi) :
    Phi lam d phi q mu R (insert u (insert v S)) - Phi lam d phi q mu R (insert u S) =
      lam * q u * (1 - q v) * (prodQ q L (countLE d (d v) L) * d v -
        ∑ k ∈ Icc (countLE d (d v) L + 1) (countLE d phi L + 1), Ck d phi q L k) + mu v := by
  set s := countLE d (d u) L with hs
  set t := countLE d (d v) L with ht
  have hst : s ≤ t := countLE_mono d hduv L
  have hspu := split_props d (d u) L hLsort
  have hspv := split_props d (d v) L hLsort
  set A := L.take s
  set M := (L.drop s).take (t - s)
  set B := L.drop t
  have eAM : L.take t = A ++ M := by
    rw [show t = s + (t - s) by omega, List.take_add]
  have eMB : L.drop s = M ++ B := by
    rw [← List.take_append_drop (t - s) (L.drop s), List.drop_drop,
      show s + (t - s) = t by omega]
  have hL : A ++ (M ++ B) = L := by rw [← eMB]; exact List.take_append_drop s L
  -- the list of S ∪ {u}
  obtain ⟨hu1, hu2, hu3⟩ := mid_props d A (M ++ B) u S (by rw [hL]; exact hLnd)
    (by rw [hL]; exact hLS) hu (by rw [hL]; exact hLsort) hspu.1
    (fun y hy => by rw [← eMB] at hy; exact (hspu.2 y hy).le)
  have hMt : ∀ y ∈ M, d y ≤ d v := fun y hy => hspv.1 y (by rw [eAM]; simp [hy])
  have hA' : ∀ y ∈ A ++ u :: M, d y ≤ d v := by
    intro y hy
    simp only [List.mem_append, List.mem_cons] at hy
    rcases hy with hy | rfl | hy
    · exact le_trans (hspu.1 y hy) hduv
    · exact hduv
    · exact hMt y hy
  have eLu : (A ++ u :: M) ++ B = A ++ u :: (M ++ B) := by simp
  have hvu : v ∉ insert u S := by simp [Ne.symm huv, hv]
  obtain ⟨hv1, hv2, hv3⟩ := mid_props d (A ++ u :: M) B v (insert u S) (by rw [eLu]; exact hu1)
    (by rw [eLu]; exact hu2) hvu (by rw [eLu]; exact hu3) hA' (fun y hy => (hspv.2 y hy).le)
  rw [Finset.insert_comm] at hv2
  have c2 : (insert u S).card ≤ R := by have := card_insert_le u S; omega
  have c3 : (insert u (insert v S)).card ≤ R := by
    have := card_insert_le u (insert v S); have := card_insert_le v S; omega
  have hu' : u ∉ insert v S := by simp [huv, hu]
  rw [cf_hv lam d phi q mu hlam hq0 hq1 hR _ _ c3 hv1 hv2 hv3,
    cf_hv lam d phi q mu hlam hq0 hq1 hR _ _ c2 hu1 hu2 hu3, sum_insert hu', sum_insert hv,
    sum_insert hu, sumCk_tail d phi q L t hLsort (countLE_mono d hdv L)]
  have hdiff := hv_insert_mid d phi q (A ++ u :: M) B v (fun y hy => le_trans (hA' y hy) hdv) hdv
  rw [eLu] at hdiff
  have e : ((A ++ u :: M).map q).prod = q u * prodQ q L t := by
    have : prodQ q L t = ((A ++ M).map q).prod := by
      show ((L.take t).map q).prod = _; rw [eAM]
    rw [this]; simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]; ring
  rw [e] at hdiff
  linear_combination lam * hdiff

theorem case2_sol {R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (hlam : 0 ≤ lam) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (hR : 1 ≤ R)
    (S : Finset (Fin J)) (u v : Fin J) (huv : u ≠ v) (hu : u ∉ S) (hv : v ∉ S)
    (hS : S.card + 2 ≤ R) (L : List (Fin J)) (hLnd : L.Nodup) (hLS : L.toFinset = S)
    (hLsort : L.Pairwise (fun a b => d a ≤ d b)) (hdvu : d v < d u) (hdu : d u ≤ phi) :
    Phi lam d phi q mu R (insert u (insert v S)) - Phi lam d phi q mu R (insert u S) =
      lam * (1 - q v) * (prodQ q L (countLE d (d v) L) * d v -
        (∑ k ∈ Icc (countLE d (d v) L + 1) (countLE d (d u) L), Ck d phi q L k +
          prodQ q L (countLE d (d u) L) * (1 - q u) * d u +
          q u * ∑ k ∈ Icc (countLE d (d u) L + 1) (countLE d phi L + 1), Ck d phi q L k)) +
        mu v := by
  set s := countLE d (d u) L with hs
  set t := countLE d (d v) L with ht
  have hts : t ≤ s := countLE_mono d hdvu.le L
  have hsn : s ≤ countLE d phi L := countLE_mono d hdu L
  have hspu := split_props d (d u) L hLsort
  have hspv := split_props d (d v) L hLsort
  set A := L.take t
  set M := (L.drop t).take (s - t)
  set B := L.drop s
  have eAM : L.take s = A ++ M := by
    rw [show s = t + (s - t) by omega, List.take_add]
  have eMB : L.drop t = M ++ B := by
    rw [← List.take_append_drop (s - t) (L.drop t), List.drop_drop,
      show t + (s - t) = s by omega]
  have hL : L.take s ++ L.drop s = L := List.take_append_drop s L
  -- the list of S ∪ {u}
  obtain ⟨hu1, hu2, hu3⟩ := mid_props d (L.take s) B u S (by rw [hL]; exact hLnd)
    (by rw [hL]; exact hLS) hu (by rw [hL]; exact hLsort) hspu.1
    (fun y hy => (hspu.2 y hy).le)
  have eLu : A ++ (M ++ u :: B) = L.take s ++ u :: B := by rw [eAM]; simp
  have hMB : ∀ y ∈ M ++ B, d v < d y := fun y hy => hspv.2 y (by rw [eMB]; exact hy)
  have hX : ∀ y ∈ M ++ u :: B, d v ≤ d y := by
    intro y hy
    simp only [List.mem_append, List.mem_cons] at hy
    rcases hy with hy | rfl | hy
    · exact (hMB y (by simp [hy])).le
    · exact hdvu.le
    · exact (hMB y (by simp [hy])).le
  have hvu : v ∉ insert u S := by simp [Ne.symm huv, hv]
  obtain ⟨hv1, hv2, hv3⟩ := mid_props d A (M ++ u :: B) v (insert u S) (by rw [eLu]; exact hu1)
    (by rw [eLu]; exact hu2) hvu (by rw [eLu]; exact hu3) hspv.1 hX
  rw [Finset.insert_comm] at hv2
  have c2 : (insert u S).card ≤ R := by have := card_insert_le u S; omega
  have c3 : (insert u (insert v S)).card ≤ R := by
    have := card_insert_le u (insert v S); have := card_insert_le v S; omega
  have hu' : u ∉ insert v S := by simp [huv, hu]
  rw [cf_hv lam d phi q mu hlam hq0 hq1 hR _ _ c3 hv1 hv2 hv3,
    cf_hv lam d phi q mu hlam hq0 hq1 hR _ _ c2 hu1 hu2 hu3, sum_insert hu', sum_insert hv,
    sum_insert hu]
  -- tails
  have Tt := sumCk_tail d phi q L t hLsort (le_trans hts hsn)
  have Ts := sumCk_tail d phi q L s hLsort hsn
  have hsplit := sum_Icc_split (fun k => Ck d phi q L k) hts (show s ≤ countLE d phi L + 1 by omega)
  rw [eMB] at Tt
  -- differences
  have d1 := hv_insert_mid d phi q A (M ++ u :: B) v
    (fun y hy => le_trans (hspv.1 y hy) (le_trans hdvu.le hdu)) (le_trans hdvu.le hdu)
  rw [eLu] at d1
  have d2 := hv_insert_mid d phi q M B u
    (fun y hy => le_trans (hspu.1 y (by rw [eAM]; simp [hy])) hdu) hdu
  have eA : (A.map q).prod = prodQ q L t := rfl
  have eS : prodQ q L s = prodQ q L t * (M.map q).prod := by
    show ((L.take s).map q).prod = _
    rw [eAM, List.map_append, List.prod_append]; rfl
  rw [eA] at d1
  linear_combination lam * d1 - lam * (1 - q v) * prodQ q L t * d2 + lam * (1 - q v) * Tt
    - lam * (1 - q v) * hsplit - lam * (1 - q v) * (1 - q u) * Ts
    + lam * (1 - q v) * (1 - q u) * (d u - RFL3Aux.hv d phi q B) * eS

end RFL3Aux

open ReliableFacilityLoc.Supermod in
theorem solution {J : ℕ} (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (L : List (Fin J))
    (hLsort : L.Pairwise (fun a b => d a ≤ d b)) (v : Fin J) (hv : d v ≤ phi) :
    prodQ q L (countLE d (d v) L) * d v -
      ∑ k ∈ Icc (countLE d (d v) L + 1) (countLE d phi L + 1), Ck d phi q L k ≤ 0 :=
  RFL3Aux.bracket_sol d phi q hq0 hq1 L hLsort v hv
