-- Prove2me | solution 1 for ReliableFacilityLoc.Supermod.proposition3_supermodular
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T23:58:41.733621+00:00
-- url     : https://prove2.me/submissions/cffbd57e-da86-4a84-98bc-7041764e37eb

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

open ReliableFacilityLoc.Supermod in
theorem solution {I J R : ℕ} (lam : Fin I → ℝ) (d : Fin I → Fin J → ℝ)
    (phi : Fin I → ℝ) (q : Fin J → ℝ) (mu : Fin I → Fin J → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (hR : 1 ≤ R) (i : Fin I) (S : Finset (Fin J))
    (u v : Fin J) (huv : u ≠ v) (hu : u ∉ S) (hv : v ∉ S) (hS : S.card + 2 ≤ R) :
    Phi (lam i) (d i) (phi i) q (mu i) R (insert u (insert v S)) -
        Phi (lam i) (d i) (phi i) q (mu i) R (insert u S) ≥
      Phi (lam i) (d i) (phi i) q (mu i) R (insert v S) -
        Phi (lam i) (d i) (phi i) q (mu i) R S := by
  set D := d i
  set L : List (Fin J) := S.toList.mergeSort (fun a b => decide (D a ≤ D b)) with hL
  have hperm := List.mergeSort_perm S.toList (fun a b => decide (D a ≤ D b))
  have hLnd : L.Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList S)
  have hLS : L.toFinset = S := by
    rw [List.toFinset_eq_of_perm _ _ hperm, Finset.toList_toFinset]
  have hLs : L.Pairwise (fun a b => D a ≤ D b) := by
    have := List.pairwise_mergeSort (le := fun a b => decide (D a ≤ D b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact le_trans hab hbc)
      (fun a b => by simpa using le_total (D a) (D b)) S.toList
    simpa using this
  obtain ⟨hvnd, hvS, hvs⟩ := RFL3Aux.ins_props D v L S hLnd hLS hv hLs
  obtain ⟨hund, huS, hus⟩ := RFL3Aux.ins_props D u L S hLnd hLS hu hLs
  have hu' : u ∉ insert v S := by simp [huv, hu]
  obtain ⟨huvnd, huvS, huvs⟩ := RFL3Aux.ins_props D u _ (insert v S) hvnd hvS hu' hvs
  have cf : ∀ (T : Finset (Fin J)) (M : List (Fin J)), T.card ≤ R → M.Nodup → M.toFinset = T →
      M.Pairwise (fun a b => D a ≤ D b) →
      Phi (lam i) D (phi i) q (mu i) R T = lam i * RFL3Aux.hv D (phi i) q M + ∑ j ∈ T, mu i j := by
    intro T M hT hMnd hMT hMs
    rw [closed_form (lam i) D (phi i) q (mu i) (hlam i) hq0 hq1 hR T hT M hMnd hMT hMs,
      RFL3Aux.sumCk_eq D (phi i) q M hMs]
  have c1 : (insert v S).card ≤ R := by have := card_insert_le v S; omega
  have c2 : (insert u S).card ≤ R := by have := card_insert_le u S; omega
  have c3 : (insert u (insert v S)).card ≤ R := by
    have := card_insert_le u (insert v S); have := card_insert_le v S; omega
  rw [cf _ _ c3 huvnd huvS huvs, cf _ _ c2 hund huS hus, cf _ _ c1 hvnd hvS hvs,
    cf _ _ (by omega) hLnd hLS hLs]
  rw [sum_insert hu', sum_insert hu, sum_insert hv]
  have key := RFL3Aux.hv_supermod D (phi i) q hq0 hq1 u v L hLs
  have := mul_le_mul_of_nonneg_left key (hlam i)
  nlinarith
