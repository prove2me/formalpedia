-- Prove2me | solution 1 for PancakeHard.property_6
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-08T12:25:58.645373+00:00
-- url     : https://prove2.me/submissions/922472ea-a1e2-42c9-b376-88b397b5b639

import Mathlib
import Definitions.Def_PancakeHard_Hook

set_option autoImplicit false

namespace PancakeHard

private def pq (xy : ℕ × ℕ) : Bool := !(xy.1 + 1 == xy.2 || xy.2 + 1 == xy.1)
private def cc (L : List ℕ) : ℕ := (L.zip L.tail).countP pq

private lemma pq_symm (a b : ℕ) : pq (a, b) = pq (b, a) := by
  unfold pq; cases h1 : (a + 1 == b) <;> cases h2 : (b + 1 == a) <;> simp_all

private lemma cc_single (a : ℕ) : cc [a] = 0 := rfl
private lemma cc_cons2 (a b : ℕ) (l : List ℕ) :
    cc (a :: b :: l) = cc (b :: l) + (if pq (a, b) then 1 else 0) := by
  simp [cc, List.countP_cons]

private lemma cc_append (A : List ℕ) (b : ℕ) (B : List ℕ) :
    cc (A ++ b :: B) = cc (A ++ [b]) + cc (b :: B) := by
  induction A with
  | nil => simp [cc_single]
  | cons a A ih =>
    cases A with
    | nil => simp [cc_cons2, cc_single]; omega
    | cons _ A'' =>
      simp only [List.cons_append] at ih ⊢
      rw [cc_cons2, cc_cons2, ih]; omega

private lemma cc_snoc (A : List ℕ) (a b : ℕ) :
    cc ((A ++ [a]) ++ [b]) = cc (A ++ [a]) + (if pq (a, b) then 1 else 0) := by
  rw [List.append_assoc, List.singleton_append, cc_append, cc_cons2, cc_single]; simp

private lemma cc_reverse (L : List ℕ) : cc L.reverse = cc L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    cases L with
    | nil => rfl
    | cons b L' =>
      rw [List.reverse_cons, List.reverse_cons, cc_snoc, ← List.reverse_cons, ih, cc_cons2, pq_symm]

private lemma bp_eq (S : List ℕ) : breakpoints S = cc S +
    (match S.getLast? with
     | none => 0
     | some x => if x = S.length then 0 else 1) := rfl

private lemma getLast_app (X : List ℕ) (b : ℕ) (B : List ℕ) :
    (X ++ b :: B).getLast? = (b :: B).getLast? := by
  cases hy : (b :: B).getLast? with
  | none => simp at hy
  | some y => rw [List.getLast?_append, hy]; rfl

private lemma bp_flip (a1 : ℕ) (A1 : List ℕ) (aL : ℕ) (hL : (a1 :: A1).getLast? = some aL)
    (b : ℕ) (B : List ℕ) :
    breakpoints ((a1 :: A1).reverse ++ b :: B) + (if pq (aL, b) then 1 else 0) =
    breakpoints ((a1 :: A1) ++ b :: B) + (if pq (a1, b) then 1 else 0) := by
  have hlen : ((a1 :: A1).reverse ++ b :: B).length = ((a1 :: A1) ++ b :: B).length := by simp; omega
  rw [bp_eq, bp_eq, hlen, getLast_app, getLast_app, cc_append, cc_append (A := a1 :: A1)]
  have h1 : cc ((a1 :: A1).reverse ++ [b]) = cc (a1 :: A1).reverse + (if pq (a1, b) then 1 else 0) := by
    rw [List.reverse_cons, cc_snoc]
  obtain ⟨A0, hA0⟩ := List.getLast?_eq_some_iff.mp hL
  have h2 : cc ((a1 :: A1) ++ [b]) = cc (a1 :: A1) + (if pq (aL, b) then 1 else 0) := by
    rw [hA0, cc_snoc]
  rw [h1, h2, cc_reverse]; omega

private lemma eff_of (a1 : ℕ) (A1 : List ℕ) (aL : ℕ) (hL : (a1 :: A1).getLast? = some aL)
    (b : ℕ) (B : List ℕ) (h1 : pq (aL, b) = true) (h2 : pq (a1, b) = false) :
    EfficientFlip ((a1 :: A1) ++ b :: B) ((a1 :: A1).reverse ++ b :: B) := by
  refine ⟨⟨(a1 :: A1).length, by simp, by simp, ?_⟩, ?_⟩
  · unfold flip; simp
  · have := bp_flip a1 A1 aL hL b B
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at this
    omega

private lemma eff_char (S S' : List ℕ) (h : EfficientFlip S S') :
    (∃ a1 A1 aL b B, (a1 :: A1).getLast? = some aL ∧ S = (a1 :: A1) ++ b :: B ∧
       S' = (a1 :: A1).reverse ++ b :: B ∧ pq (aL, b) = true ∧ pq (a1, b) = false) ∨
    (∃ a1, S.head? = some a1 ∧ a1 = S.length) := by
  obtain ⟨⟨r, hr1, hr2, rfl⟩, hb⟩ := h
  have hne : S.take r ≠ [] := by
    intro h0; rw [List.take_eq_nil_iff] at h0
    rcases h0 with h0 | h0
    · omega
    · subst h0; simp at hr2; omega
  obtain ⟨a1, A1, hA⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨aL, hL⟩ : ∃ aL, (a1 :: A1).getLast? = some aL :=
    ⟨(a1 :: A1).getLast (by simp), List.getLast?_eq_some_getLast _⟩
  have hS := (List.take_append_drop r S).symm
  unfold flip at hb ⊢
  rw [hA] at hS hb ⊢
  cases hB : S.drop r with
  | cons b B =>
    rw [hB] at hS hb
    left
    refine ⟨a1, A1, aL, b, B, hL, hS, rfl, ?_⟩
    have key := bp_flip a1 A1 aL hL b B
    rw [← hS] at key
    generalize breakpoints ((a1 :: A1).reverse ++ b :: B) = X at key hb
    generalize breakpoints S = Y at key hb
    clear hS hB hA hne hr1 hr2
    cases h1 : pq (aL, b) <;> cases h2 : pq (a1, b) <;>
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at key ⊢ <;>
      first | (exfalso; omega) | simp
  | nil =>
    rw [hB] at hS hb
    right
    refine ⟨a1, by rw [hS]; simp, ?_⟩
    rw [List.append_nil] at hS hb
    rw [hS] at hb
    rw [bp_eq, bp_eq, cc_reverse, List.getLast?_reverse, hL, List.length_reverse] at hb
    simp only [List.head?_cons] at hb
    rw [hS]
    split_ifs at hb <;> omega

private lemma split_uniq (x : ℕ) : ∀ (L1 L2 A B : List ℕ), (L1 ++ x :: L2).Nodup →
    L1 ++ x :: L2 = A ++ x :: B → A = L1 ∧ B = L2
  | [], L2, [], B, _, h => by simp at h; exact ⟨rfl, h.symm⟩
  | [], L2, a :: A, B, hn, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp at hn
  | l :: L1, L2, [], B, hn, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp at hn
  | l :: L1, L2, a :: A, B, hn, h => by
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have := split_uniq x L1 L2 A B (List.nodup_cons.mp hn).2 h
      exact ⟨by rw [this.1], this.2⟩

private lemma memS (S : List ℕ) (hS : IsStack S) (x : ℕ) (hx : x ∈ S) : 1 ≤ x ∧ x ≤ S.length := by
  have := hS.mem_iff.mp hx
  unfold identity interval at this
  rw [List.mem_range'_1] at this; omega

private lemma stack_nodup (S : List ℕ) (hS : IsStack S) : S.Nodup := by
  refine hS.nodup_iff.mpr ?_
  unfold identity interval; exact List.nodup_range' ..

private lemma identity_head (n : ℕ) (hn : 1 ≤ n) : (identity n).head? = some 1 := by
  unfold identity interval
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 + 1 - 1 = m + 1 by omega, List.range'_succ]; rfl

private lemma pq_false_iff (a b : ℕ) : pq (a, b) = false ↔ (a + 1 = b ∨ b + 1 = a) := by
  unfold pq; cases h1 : (a + 1 == b) <;> cases h2 : (b + 1 == a) <;> simp_all

private lemma pq_true_iff (a b : ℕ) : pq (a, b) = true ↔ ¬(a + 1 = b ∨ b + 1 = a) := by
  unfold pq; cases h1 : (a + 1 == b) <;> cases h2 : (b + 1 == a) <;> simp_all


private lemma hookG_eq (p : ℕ) : hookG p = [p + 3, p + 4] := by simp [hookG, shift]
private lemma hookH_eq (p : ℕ) :
    hookH p = [p + 12, p + 11, p + 6, p + 5, p + 9, p + 8, p + 2, p + 1] := by
  simp [hookH, shift]
private lemma hookG'_eq (p : ℕ) :
    hookG' p = [p + 12, p + 11, p + 6, p + 5, p + 4, p + 3] := by simp [hookG', shift]
private lemma hookH'_eq (p : ℕ) :
    hookH' p = [p + 10, p + 9, p + 8, p + 2, p + 1] := by simp [hookH', shift]
private lemma hookG''_eq (p : ℕ) :
    hookG'' p = [p + 3, p + 4, p + 5, p + 6, p + 7] := by simp [hookG'', shift]
private lemma hookH''_eq (p : ℕ) :
    hookH'' p = [p + 12, p + 11, p + 10, p + 9, p + 8, p + 2, p + 1] := by
  simp [hookH'', shift]

private lemma pref_getLast (p : ℕ) (X Y : List ℕ) :
    (((p + 10) :: X ++ [p + 3, p + 4] ++ Y ++ [p + 12, p + 11, p + 6, p + 5])).getLast? =
      some (p + 5) :=
  List.getLast?_eq_some_iff.mpr ⟨(p + 10) :: X ++ [p + 3, p + 4] ++ Y ++ [p + 12, p + 11, p + 6], by simp⟩

private lemma pref_reverse (p : ℕ) (X Y : List ℕ) :
    ((p + 10) :: X ++ [p + 3, p + 4] ++ Y ++ [p + 12, p + 11, p + 6, p + 5]).reverse =
      [p + 5, p + 6, p + 11, p + 12] ++ Y.reverse ++ [p + 4, p + 3] ++ X.reverse ++ [p + 10] := by
  -- expand appends then reverse_cons repeatedly
  have h :
      (p + 10) :: X ++ [p + 3, p + 4] ++ Y ++ [p + 12, p + 11, p + 6, p + 5] =
        (((((p + 10) :: X ++ [p + 3]) ++ [p + 4]) ++ Y ++ [p + 12]) ++ [p + 11]) ++ [p + 6] ++ [p + 5] := by
    simp [List.append_assoc]
  rw [h]
  simp [List.reverse_append, List.reverse_cons, List.append_assoc]


private lemma getLast_snoc (A : List ℕ) (a : ℕ) : (A ++ [a]).getLast? = some a :=
  List.getLast?_concat

private lemma ne_of_nodup_mem {x : ℕ} {A B : List ℕ}
    (hnd : (A ++ B).Nodup) (hA : x ∈ A) (hB : x ∈ B) : False := by
  have hle := (List.nodup_iff_count_le_one.mp hnd) x
  have : 2 ≤ List.count x (A ++ B) := by
    rw [List.count_append]
    have := List.count_pos_iff.mpr hA
    have := List.count_pos_iff.mpr hB
    omega
  omega



private lemma y_ne_hook_G (p : ℕ) (X Y Z : List ℕ) (y : ℕ)
    (hnd : ((p + 10) :: X ++ [p+3, p+4] ++ Y ++
      [p+12, p+11, p+6, p+5, p+9, p+8, p+2, p+1] ++ Z).Nodup)
    (hy : y ∈ Y) (hz : y ∈ ([p+3, p+4] : List ℕ)) : False := by
  have hle := (List.nodup_iff_count_le_one.mp hnd) y
  have hS' : ((p + 10) :: X ++ [p+3, p+4] ++ Y ++
      [p+12, p+11, p+6, p+5, p+9, p+8, p+2, p+1] ++ Z) =
    ((p + 10) :: X ++ [p+3, p+4]) ++ (Y ++
      ([p+12, p+11, p+6, p+5, p+9, p+8, p+2, p+1] ++ Z)) := by
    simp [List.append_assoc]
  rw [hS'] at hle
  have : 2 ≤ List.count y (((p + 10) :: X ++ [p+3, p+4]) ++
      (Y ++ ([p+12, p+11, p+6, p+5, p+9, p+8, p+2, p+1] ++ Z))) := by
    rw [List.count_append]
    have c1 : 1 ≤ List.count y ((p + 10) :: X ++ [p+3, p+4]) :=
      List.count_pos_iff.mpr (by simp [hz])
    have c2 : 1 ≤ List.count y (Y ++
        ([p+12, p+11, p+6, p+5, p+9, p+8, p+2, p+1] ++ Z)) := by
      rw [List.count_append]; have := List.count_pos_iff.mpr hy; omega
    omega
  omega

private lemma y_ne_hook_H (p : ℕ) (X Y Z : List ℕ) (y : ℕ)
    (hnd : ((p + 10) :: X ++ [p+3, p+4] ++ Y ++
      [p+12, p+11, p+6, p+5, p+9, p+8, p+2, p+1] ++ Z).Nodup)
    (hy : y ∈ Y)
    (hz : y ∈ ([p+12, p+11, p+6, p+5, p+9, p+8, p+2, p+1] : List ℕ)) : False := by
  have hle := (List.nodup_iff_count_le_one.mp hnd) y
  have hS' : ((p + 10) :: X ++ [p+3, p+4] ++ Y ++
      [p+12, p+11, p+6, p+5, p+9, p+8, p+2, p+1] ++ Z) =
    ((p + 10) :: X ++ [p+3, p+4] ++ Y) ++
      ([p+12, p+11, p+6, p+5, p+9, p+8, p+2, p+1] ++ Z) := by
    simp [List.append_assoc]
  rw [hS'] at hle
  have : 2 ≤ List.count y (((p + 10) :: X ++ [p+3, p+4] ++ Y) ++
      ([p+12, p+11, p+6, p+5, p+9, p+8, p+2, p+1] ++ Z)) := by
    rw [List.count_append]
    have c1 : 1 ≤ List.count y ((p + 10) :: X ++ [p+3, p+4] ++ Y) := by
      have : (p + 10) :: X ++ [p+3, p+4] ++ Y =
          ((p + 10) :: X ++ [p+3, p+4]) ++ Y := by simp [List.append_assoc]
      rw [this, List.count_append]; have := List.count_pos_iff.mpr hy; omega
    have c2 : 1 ≤ List.count y ([p+12, p+11, p+6, p+5, p+9, p+8, p+2, p+1] ++ Z) :=
      List.count_pos_iff.mpr (List.mem_append_left _ hz)
    omega
  omega


private lemma y_ne_put_G (p : ℕ) (X Y Z : List ℕ) (y : ℕ)
    (hnd : ((p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3] ++ Y.reverse ++
      [p+10, p+9, p+8, p+2, p+1] ++ Z).Nodup)
    (hy : y ∈ Y.reverse)
    (hz : y ∈ ([p+12, p+11, p+6, p+5, p+4, p+3] : List ℕ)) : False := by
  have hle := (List.nodup_iff_count_le_one.mp hnd) y
  have hS' : ((p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3] ++ Y.reverse ++
      [p+10, p+9, p+8, p+2, p+1] ++ Z) =
    ((p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3]) ++
      (Y.reverse ++ ([p+10, p+9, p+8, p+2, p+1] ++ Z)) := by
    simp [List.append_assoc]
  rw [hS'] at hle
  have : 2 ≤ List.count y (((p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3]) ++
      (Y.reverse ++ ([p+10, p+9, p+8, p+2, p+1] ++ Z))) := by
    rw [List.count_append]
    have c1 : 1 ≤ List.count y ((p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3]) :=
      List.count_pos_iff.mpr (by simp [hz])
    have c2 : 1 ≤ List.count y (Y.reverse ++ ([p+10, p+9, p+8, p+2, p+1] ++ Z)) := by
      rw [List.count_append]; have := List.count_pos_iff.mpr hy; omega
    omega
  omega

private lemma y_ne_put_H (p : ℕ) (X Y Z : List ℕ) (y : ℕ)
    (hnd : ((p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3] ++ Y.reverse ++
      [p+10, p+9, p+8, p+2, p+1] ++ Z).Nodup)
    (hy : y ∈ Y.reverse)
    (hz : y ∈ ([p+10, p+9, p+8, p+2, p+1] : List ℕ)) : False := by
  have hle := (List.nodup_iff_count_le_one.mp hnd) y
  have hS' : ((p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3] ++ Y.reverse ++
      [p+10, p+9, p+8, p+2, p+1] ++ Z) =
    ((p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3] ++ Y.reverse) ++
      ([p+10, p+9, p+8, p+2, p+1] ++ Z) := by
    simp [List.append_assoc]
  rw [hS'] at hle
  have : 2 ≤ List.count y (((p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3] ++ Y.reverse) ++
      ([p+10, p+9, p+8, p+2, p+1] ++ Z)) := by
    rw [List.count_append]
    have c1 : 1 ≤ List.count y ((p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3] ++ Y.reverse) := by
      have : (p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3] ++ Y.reverse =
          ((p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3]) ++ Y.reverse := by
        simp [List.append_assoc]
      rw [this, List.count_append]; have := List.count_pos_iff.mpr hy; omega
    have c2 : 1 ≤ List.count y ([p+10, p+9, p+8, p+2, p+1] ++ Z) :=
      List.count_pos_iff.mpr (List.mem_append_left _ hz)
    omega
  omega

private lemma y_ne_rel_G (p : ℕ) (X Y : List ℕ) (y : ℕ)
    (hnd : ([p+3, p+4, p+5, p+6, p+7] ++ X ++
      [p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y).Nodup)
    (hy : y ∈ Y)
    (hz : y ∈ ([p+3, p+4, p+5, p+6, p+7] : List ℕ)) : False := by
  have hle := (List.nodup_iff_count_le_one.mp hnd) y
  have hS' : ([p+3, p+4, p+5, p+6, p+7] ++ X ++
      [p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y) =
    [p+3, p+4, p+5, p+6, p+7] ++ (X ++ [p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y) := by
    simp [List.append_assoc]
  rw [hS'] at hle
  have : 2 ≤ List.count y ([p+3, p+4, p+5, p+6, p+7] ++
      (X ++ [p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y)) := by
    rw [List.count_append]
    have c1 : 1 ≤ List.count y [p+3, p+4, p+5, p+6, p+7] :=
      List.count_pos_iff.mpr hz
    have c2 : 1 ≤ List.count y (X ++ [p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y) := by
      have : X ++ [p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y =
          (X ++ [p+12, p+11, p+10, p+9, p+8, p+2, p+1]) ++ Y := by simp [List.append_assoc]
      rw [this, List.count_append]; have := List.count_pos_iff.mpr hy; omega
    omega
  omega

private lemma x_ne_rel_H (p : ℕ) (X Y : List ℕ) (x : ℕ)
    (hnd : ([p+3, p+4, p+5, p+6, p+7] ++ X ++
      [p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y).Nodup)
    (hx : x ∈ X)
    (hz : x ∈ ([p+12, p+11, p+10, p+9, p+8, p+2, p+1] : List ℕ)) : False := by
  have hle := (List.nodup_iff_count_le_one.mp hnd) x
  have hS' : ([p+3, p+4, p+5, p+6, p+7] ++ X ++
      [p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y) =
    ([p+3, p+4, p+5, p+6, p+7] ++ X) ++
      ([p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y) := by
    simp [List.append_assoc]
  rw [hS'] at hle
  have : 2 ≤ List.count x (([p+3, p+4, p+5, p+6, p+7] ++ X) ++
      ([p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y)) := by
    rw [List.count_append]
    have c1 : 1 ≤ List.count x ([p+3, p+4, p+5, p+6, p+7] ++ X) := by
      rw [List.count_append]; have := List.count_pos_iff.mpr hx; omega
    have c2 : 1 ≤ List.count x ([p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y) :=
      List.count_pos_iff.mpr (List.mem_append_left _ hz)
    omega
  omega

/-- Property 6(a): take opens the hook (two unique efficient flips). -/
theorem prop6_a (p : ℕ) (X Y Z : List ℕ)
    (hS : IsStack (hookTake p :: X ++ hookG p ++ Y ++ hookH p ++ Z)) :
    LeadsTo (hookTake p :: X ++ hookG p ++ Y ++ hookH p ++ Z)
      {Y ++ hookG' p ++ X.reverse ++ hookH' p ++ Z} := by
  set S := hookTake p :: X ++ hookG p ++ Y ++ hookH p ++ Z with hSdef
  have hnd := stack_nodup S hS
  have hmem := memS S hS
  rw [show hookTake p = p + 10 by rfl, hookG_eq, hookH_eq] at hSdef
  -- S = (p+10)::X ++ [p+3,p+4] ++ Y ++ [p+12,p+11,p+6,p+5,p+9,p+8,p+2,p+1] ++ Z
  set S1 := [p+5, p+6, p+11, p+12] ++ Y.reverse ++ [p+4, p+3] ++ X.reverse ++
      [p+10, p+9, p+8, p+2, p+1] ++ Z with hS1def
  set T := Y ++ [p+12, p+11, p+6, p+5, p+4, p+3] ++ X.reverse ++
      [p+10, p+9, p+8, p+2, p+1] ++ Z with hTdef
  have hT_hook : T = Y ++ hookG' p ++ X.reverse ++ hookH' p ++ Z := by
    simp [hTdef, hookG'_eq, hookH'_eq, List.append_assoc]
  -- first-flip split: through p+5, join p+9
  have hSd : S = ((p + 10) :: X ++ [p+3, p+4] ++ Y ++ [p+12, p+11, p+6, p+5]) ++
      (p + 9) :: ([p+8, p+2, p+1] ++ Z) := by
    rw [hSdef]; simp [List.append_assoc]
  have hpref_last :
      ((p + 10) :: X ++ [p+3, p+4] ++ Y ++ [p+12, p+11, p+6, p+5]).getLast? =
        some (p + 5) := by
    rw [show (p + 10) :: X ++ [p+3, p+4] ++ Y ++ [p+12, p+11, p+6, p+5] =
          ((p + 10) :: X ++ [p+3, p+4] ++ Y ++ [p+12, p+11, p+6]) ++ [p + 5] by simp]
    exact getLast_snoc _ _
  have hS1eq : S1 =
      ((p + 10) :: X ++ [p+3, p+4] ++ Y ++ [p+12, p+11, p+6, p+5]).reverse ++
        (p + 9) :: ([p+8, p+2, p+1] ++ Z) := by
    have h :
        (p + 10) :: X ++ [p+3, p+4] ++ Y ++ [p+12, p+11, p+6, p+5] =
          (((((p + 10) :: X ++ [p+3]) ++ [p+4]) ++ Y ++ [p+12]) ++ [p+11]) ++ [p+6] ++ [p+5] := by
      simp [List.append_assoc]
    rw [hS1def, h]
    simp [List.reverse_append, List.reverse_cons, List.append_assoc]
  have eff1 : EfficientFlip S S1 := by
    have h := eff_of (p + 10) (X ++ [p+3, p+4] ++ Y ++ [p+12, p+11, p+6, p+5]) (p + 5)
      (by simpa [List.cons_append, List.append_assoc] using hpref_last)
      (p + 9) ([p+8, p+2, p+1] ++ Z)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    simpa [hSd, hS1eq, List.cons_append] using h
  -- second-flip split: through end of [p+5..p+12]++⋆Y, join p+4
  have hS1d : S1 = ([p+5, p+6, p+11, p+12] ++ Y.reverse) ++
      (p + 4) :: ([p+3] ++ X.reverse ++ [p+10, p+9, p+8, p+2, p+1] ++ Z) := by
    simp [hS1def, List.append_assoc]
  have hTeq : T = ([p+5, p+6, p+11, p+12] ++ Y.reverse).reverse ++
      (p + 4) :: ([p+3] ++ X.reverse ++ [p+10, p+9, p+8, p+2, p+1] ++ Z) := by
    simp [hTdef, List.reverse_append, List.reverse_cons, List.append_assoc]
  have eff2 : EfficientFlip S1 T := by
    cases hY : Y with
    | nil =>
      have hL : ([p+5, p+6, p+11, p+12] ++ Y.reverse).getLast? = some (p + 12) := by
        rw [hY]; change ([p+5, p+6, p+11] ++ [p+12]).getLast? = some (p + 12)
        exact getLast_snoc _ _
      have h := eff_of (p + 5) ([p+6, p+11, p+12] ++ Y.reverse) (p + 12)
        (by simpa [List.cons_append, hY] using hL)
        (p + 4) ([p+3] ++ X.reverse ++ [p+10, p+9, p+8, p+2, p+1] ++ Z)
        (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
      simpa [hS1d, hTeq, List.cons_append, hY] using h
    | cons y Y' =>
      have hnd0 : ((p + 10) :: X ++ [p+3, p+4] ++ Y ++
          [p+12, p+11, p+6, p+5, p+9, p+8, p+2, p+1] ++ Z).Nodup := by
        simpa [hSdef] using hnd
      have hyY : y ∈ Y := by simp [hY]
      have hy_ne3 : y ≠ p + 3 := fun h => y_ne_hook_G p X Y Z y hnd0 hyY (by simp [h])
      have hy_ne4 : y ≠ p + 4 := fun h => y_ne_hook_G p X Y Z y hnd0 hyY (by simp [h])
      have hy_ne5 : y ≠ p + 5 := fun h => y_ne_hook_H p X Y Z y hnd0 hyY (by simp [h])
      have hL : ([p+5, p+6, p+11, p+12] ++ Y.reverse).getLast? = some y := by
        rw [hY, List.reverse_cons, ← List.append_assoc]; exact getLast_snoc _ _
      have h := eff_of (p + 5) ([p+6, p+11, p+12] ++ Y.reverse) y
        (by simpa [List.cons_append] using hL)
        (p + 4) ([p+3] ++ X.reverse ++ [p+10, p+9, p+8, p+2, p+1] ++ Z)
        (by rw [pq_true_iff]; clear hL; omega) (by rw [pq_false_iff]; omega)
      simpa [hS1d, hTeq, List.cons_append] using h
  have hperm1 : S1.Perm S := by
    rw [hS1eq, hSd]; exact (List.reverse_perm _).append_right _
  have hlen1 : S1.length = S.length := hperm1.length_eq
  have hS1stack : IsStack S1 := by unfold IsStack; rw [hlen1]; exact hperm1.trans hS
  have hnd1 := stack_nodup S1 hS1stack
  have hSne : S ≠ identity S.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ S.length := by
      have := (hmem (p + 10) (by simp [hSdef])).2; omega
    have hid := identity_head _ hn0
    have hhd : S.head? = some (p + 10) := by simp [hSdef]
    rw [hid, hhd] at hh; injection hh with hh; omega
  have hS1ne : S1 ≠ identity S.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ S.length := by
      have := (hmem (p + 10) (by simp [hSdef])).2; omega
    have hid := identity_head _ hn0
    have hhd : S1.head? = some (p + 5) := by simp [hS1def]
    rw [hid, hhd] at hh; injection hh with hh; omega
  have step1 : ∀ B, EfficientFlip S B → B = S1 := by
    intro B hB
    rcases eff_char S B hB with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 10 := by
        have := congrArg List.head? (hSdef.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · -- a1+1 = b => b = p+11 (bad)
        subst h2
        have hSdAlt : S = ((p + 10) :: X ++ [p+3, p+4] ++ Y ++ [p+12]) ++
            (p + 11) :: ([p+6, p+5, p+9, p+8, p+2, p+1] ++ Z) := by
          rw [hSdef]; simp [List.append_assoc]
        obtain ⟨e1, -⟩ := split_uniq (p + 11)
          ((p + 10) :: X ++ [p+3, p+4] ++ Y ++ [p+12]) _
          ((p + 10) :: A1) B' (hSdAlt ▸ hnd) (hSdAlt.symm.trans hSe)
        have hL' : ((p + 10) :: X ++ [p+3, p+4] ++ Y ++ [p+12]).getLast? = some (p + 12) := by
          rw [show (p + 10) :: X ++ [p+3, p+4] ++ Y ++ [p+12] =
                ((p + 10) :: X ++ [p+3, p+4] ++ Y) ++ [p + 12] by simp]
          exact getLast_snoc _ _
        rw [e1, hL'] at hL; injection hL with hL; subst hL
        rw [pq_true_iff] at h1; omega
      · -- b+1 = a1 => b = p+9 (good)
        have hb : b = p + 9 := by omega
        subst hb
        obtain ⟨e1, e2⟩ := split_uniq (p + 9)
          ((p + 10) :: X ++ [p+3, p+4] ++ Y ++ [p+12, p+11, p+6, p+5])
          ([p+8, p+2, p+1] ++ Z) ((p + 10) :: A1) B' (hSd ▸ hnd) (hSd.symm.trans hSe)
        rw [hBe, e1, e2, ← hS1eq]
    · exfalso
      rw [hSdef] at hh1; simp [ha1] at hh1
      have := (hmem (p + 12) (by simp [hSdef])).2; omega
  have step2 : ∀ C, EfficientFlip S1 C → C = T := by
    intro C hC
    rcases eff_char S1 C hC with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 5 := by
        have := congrArg List.head? (hS1def.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · -- a1+1 = b => b = p+6 (bad)
        subst h2
        have hSdAlt : S1 = [p+5] ++ (p + 6) ::
            ([p+11, p+12] ++ Y.reverse ++ [p+4, p+3] ++ X.reverse ++
              [p+10, p+9, p+8, p+2, p+1] ++ Z) := by
          simp [hS1def, List.append_assoc]
        obtain ⟨e1, -⟩ := split_uniq (p + 6) [p+5] _
          ((p + 5) :: A1) B' (hSdAlt ▸ hnd1) (hSdAlt.symm.trans hSe)
        rw [e1] at hL; simp at hL; subst hL
        rw [pq_true_iff] at h1; omega
      · -- b+1 = a1 => b = p+4 (good)
        have hb : b = p + 4 := by omega
        subst hb
        obtain ⟨e1, e2⟩ := split_uniq (p + 4)
          ([p+5, p+6, p+11, p+12] ++ Y.reverse)
          ([p+3] ++ X.reverse ++ [p+10, p+9, p+8, p+2, p+1] ++ Z)
          ((p + 5) :: A1) B' (hS1d ▸ hnd1) (hS1d.symm.trans hSe)
        rw [hBe, e1, e2, ← hTeq]
    · exfalso
      rw [hS1def] at hh1; simp [ha1] at hh1
      have := (memS S1 hS1stack (p + 12) (by simp [hS1def])).2; omega
  refine ⟨?exist, ?unique⟩
  · intro T' hT'; rw [Set.mem_singleton_iff] at hT'; subst hT'
    refine ⟨[S, S1, T], rfl, ?_, ?_⟩
    · simpa [hT_hook] using (rfl : [S, S1, T].getLast? = some T)
    · exact List.isChain_cons_cons.mpr ⟨eff1,
        List.isChain_cons_cons.mpr ⟨eff2, List.isChain_singleton _⟩⟩
  · intro π hπ
    obtain ⟨hh, hl, hc⟩ := hπ
    rcases π with _ | ⟨A, _ | ⟨B, rest⟩⟩
    · simp at hh
    · simp at hh hl; exact absurd (hh ▸ hl) hSne
    · simp only [List.head?_cons, Option.some.injEq] at hh; subst hh
      rw [List.isChain_cons_cons] at hc
      have hB := step1 B hc.1; subst hB
      rcases rest with _ | ⟨C, rest'⟩
      · simp at hl; exact absurd hl hS1ne
      · rw [List.isChain_cons_cons] at hc
        have hC := step2 C hc.2.1; subst hC
        exact ⟨T, by simp [hT_hook], by simp⟩


/-- Property 6(b): put closes the hook (two unique efficient flips). -/
theorem prop6_b (p : ℕ) (X Y Z : List ℕ)
    (hS : IsStack (hookPut p :: X ++ hookG' p ++ Y.reverse ++ hookH' p ++ Z)) :
    LeadsTo (hookPut p :: X ++ hookG' p ++ Y.reverse ++ hookH' p ++ Z)
      {Y ++ hookG'' p ++ X ++ hookH'' p ++ Z} := by
  set S := hookPut p :: X ++ hookG' p ++ Y.reverse ++ hookH' p ++ Z with hSdef
  have hnd := stack_nodup S hS
  have hmem := memS S hS
  rw [show hookPut p = p + 7 by rfl, hookG'_eq, hookH'_eq] at hSdef
  set S1 := [p+11, p+12] ++ X.reverse ++ [p+7, p+6, p+5, p+4, p+3] ++ Y.reverse ++
      [p+10, p+9, p+8, p+2, p+1] ++ Z with hS1def
  set T := Y ++ [p+3, p+4, p+5, p+6, p+7] ++ X ++
      [p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Z with hTdef
  have hT_hook : T = Y ++ hookG'' p ++ X ++ hookH'' p ++ Z := by
    simp [hTdef, hookG''_eq, hookH''_eq, List.append_assoc]
  have hSd : S = ((p + 7) :: X ++ [p+12, p+11]) ++
      (p + 6) :: ([p+5, p+4, p+3] ++ Y.reverse ++ [p+10, p+9, p+8, p+2, p+1] ++ Z) := by
    rw [hSdef]; simp [List.append_assoc]
  have hpref_last : ((p + 7) :: X ++ [p+12, p+11]).getLast? = some (p + 11) := by
    rw [show (p + 7) :: X ++ [p+12, p+11] = ((p + 7) :: X ++ [p+12]) ++ [p + 11] by simp]
    exact getLast_snoc _ _
  have hS1eq : S1 = ((p + 7) :: X ++ [p+12, p+11]).reverse ++
      (p + 6) :: ([p+5, p+4, p+3] ++ Y.reverse ++ [p+10, p+9, p+8, p+2, p+1] ++ Z) := by
    simp [hS1def, List.reverse_append, List.reverse_cons, List.append_assoc]
  have eff1 : EfficientFlip S S1 := by
    have h := eff_of (p + 7) (X ++ [p+12, p+11]) (p + 11)
      (by simpa [List.cons_append] using hpref_last)
      (p + 6) ([p+5, p+4, p+3] ++ Y.reverse ++ [p+10, p+9, p+8, p+2, p+1] ++ Z)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    simpa [hSd, hS1eq, List.cons_append] using h
  have hS1d : S1 = ([p+11, p+12] ++ X.reverse ++ [p+7, p+6, p+5, p+4, p+3] ++ Y.reverse) ++
      (p + 10) :: ([p+9, p+8, p+2, p+1] ++ Z) := by
    simp [hS1def, List.append_assoc]
  have hTeq : T = ([p+11, p+12] ++ X.reverse ++ [p+7, p+6, p+5, p+4, p+3] ++ Y.reverse).reverse ++
      (p + 10) :: ([p+9, p+8, p+2, p+1] ++ Z) := by
    simp [hTdef, List.reverse_append, List.reverse_cons, List.append_assoc]
  have eff2 : EfficientFlip S1 T := by
    cases hY : Y with
    | nil =>
      have hL : ([p+11, p+12] ++ X.reverse ++ [p+7, p+6, p+5, p+4, p+3] ++ Y.reverse).getLast? =
          some (p + 3) := by
        rw [hY, List.reverse_nil]
        rw [show [p+11, p+12] ++ X.reverse ++ [p+7, p+6, p+5, p+4, p+3] ++ ([] : List ℕ) =
              ([p+11, p+12] ++ X.reverse ++ [p+7, p+6, p+5, p+4]) ++ [p + 3] by simp]
        exact getLast_snoc _ _
      have h := eff_of (p + 11)
        ([p+12] ++ X.reverse ++ [p+7, p+6, p+5, p+4, p+3] ++ Y.reverse) (p + 3)
        (by simpa [List.cons_append, hY, List.append_assoc] using hL)
        (p + 10) ([p+9, p+8, p+2, p+1] ++ Z)
        (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
      simpa [hS1d, hTeq, List.cons_append, hY] using h
    | cons y Y' =>
      have hnd0 : ((p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3] ++ Y.reverse ++
          [p+10, p+9, p+8, p+2, p+1] ++ Z).Nodup := by
        simpa [hSdef] using hnd
      have hyY : y ∈ Y.reverse := by simp [hY]
      have hy_ne9 : y ≠ p + 9 := fun h => y_ne_put_H p X Y Z y hnd0 hyY (by simp [h])
      have hy_ne11 : y ≠ p + 11 := fun h => y_ne_put_G p X Y Z y hnd0 hyY (by simp [h])
      have hL : ([p+11, p+12] ++ X.reverse ++ [p+7, p+6, p+5, p+4, p+3] ++ Y.reverse).getLast? =
          some y := by
        rw [hY, List.reverse_cons, ← List.append_assoc]; exact getLast_snoc _ _
      have h := eff_of (p + 11)
        ([p+12] ++ X.reverse ++ [p+7, p+6, p+5, p+4, p+3] ++ Y.reverse) y
        (by simpa [List.cons_append] using hL)
        (p + 10) ([p+9, p+8, p+2, p+1] ++ Z)
        (by rw [pq_true_iff]; clear hL; omega) (by rw [pq_false_iff]; omega)
      simpa [hS1d, hTeq, List.cons_append] using h
  have hperm1 : S1.Perm S := by
    rw [hS1eq, hSd]; exact (List.reverse_perm _).append_right _
  have hlen1 : S1.length = S.length := hperm1.length_eq
  have hS1stack : IsStack S1 := by unfold IsStack; rw [hlen1]; exact hperm1.trans hS
  have hnd1 := stack_nodup S1 hS1stack
  have hSne : S ≠ identity S.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ S.length := by
      have := (hmem (p + 7) (by simp [hSdef])).2; omega
    have hid := identity_head _ hn0
    have hhd : S.head? = some (p + 7) := by simp [hSdef]
    rw [hid, hhd] at hh; injection hh with hh; omega
  have hS1ne : S1 ≠ identity S.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ S.length := by
      have := (hmem (p + 7) (by simp [hSdef])).2; omega
    have hid := identity_head _ hn0
    have hhd : S1.head? = some (p + 11) := by simp [hS1def]
    rw [hid, hhd] at hh; injection hh with hh; omega
  have step1 : ∀ B, EfficientFlip S B → B = S1 := by
    intro B hB
    rcases eff_char S B hB with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 7 := by
        have := congrArg List.head? (hSdef.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · -- a1+1 = b => b = p+8 (bad): prefix ends at p+9, adjacent to p+8
        subst h2
        have hSdAlt : S = ((p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3] ++ Y.reverse ++
            [p+10, p+9]) ++ (p + 8) :: ([p+2, p+1] ++ Z) := by
          rw [hSdef]; simp [List.append_assoc]
        obtain ⟨e1, -⟩ := split_uniq (p + 8)
          ((p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3] ++ Y.reverse ++ [p+10, p+9]) _
          ((p + 7) :: A1) B' (hSdAlt ▸ hnd) (hSdAlt.symm.trans hSe)
        have hL' : ((p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3] ++ Y.reverse ++
            [p+10, p+9]).getLast? = some (p + 9) := by
          rw [show (p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3] ++ Y.reverse ++ [p+10, p+9] =
                ((p + 7) :: X ++ [p+12, p+11, p+6, p+5, p+4, p+3] ++ Y.reverse ++ [p+10]) ++ [p + 9] by simp]
          exact getLast_snoc _ _
        rw [e1, hL'] at hL; injection hL with hL; subst hL
        rw [pq_true_iff] at h1; omega
      · -- b+1 = a1 => b = p+6 (good)
        have hb : b = p + 6 := by omega
        subst hb
        obtain ⟨e1, e2⟩ := split_uniq (p + 6)
          ((p + 7) :: X ++ [p+12, p+11])
          ([p+5, p+4, p+3] ++ Y.reverse ++ [p+10, p+9, p+8, p+2, p+1] ++ Z)
          ((p + 7) :: A1) B' (hSd ▸ hnd) (hSd.symm.trans hSe)
        rw [hBe, e1, e2, ← hS1eq]
    · exfalso
      rw [hSdef] at hh1; simp [ha1] at hh1
      have := (hmem (p + 12) (by simp [hSdef])).2; omega
  have step2 : ∀ C, EfficientFlip S1 C → C = T := by
    intro C hC
    rcases eff_char S1 C hC with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 11 := by
        have := congrArg List.head? (hS1def.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · -- a1+1 = b => b = p+12 (bad)
        subst h2
        have hSdAlt : S1 = [p+11] ++ (p + 12) ::
            (X.reverse ++ [p+7, p+6, p+5, p+4, p+3] ++ Y.reverse ++
              [p+10, p+9, p+8, p+2, p+1] ++ Z) := by
          simp [hS1def, List.append_assoc]
        obtain ⟨e1, -⟩ := split_uniq (p + 12) [p+11] _
          ((p + 11) :: A1) B' (hSdAlt ▸ hnd1) (hSdAlt.symm.trans hSe)
        rw [e1] at hL; simp at hL; subst hL
        rw [pq_true_iff] at h1; omega
      · -- b+1 = a1 => b = p+10 (good)
        have hb : b = p + 10 := by omega
        subst hb
        obtain ⟨e1, e2⟩ := split_uniq (p + 10)
          ([p+11, p+12] ++ X.reverse ++ [p+7, p+6, p+5, p+4, p+3] ++ Y.reverse)
          ([p+9, p+8, p+2, p+1] ++ Z)
          ((p + 11) :: A1) B' (hS1d ▸ hnd1) (hS1d.symm.trans hSe)
        rw [hBe, e1, e2, ← hTeq]
    · exfalso
      rw [hS1def] at hh1; simp [ha1] at hh1
      have := (memS S1 hS1stack (p + 12) (by simp [hS1def])).2; omega
  refine ⟨?exist, ?unique⟩
  · intro T' hT'; rw [Set.mem_singleton_iff] at hT'; subst hT'
    refine ⟨[S, S1, T], rfl, ?_, ?_⟩
    · simpa [hT_hook] using (rfl : [S, S1, T].getLast? = some T)
    · exact List.isChain_cons_cons.mpr ⟨eff1,
        List.isChain_cons_cons.mpr ⟨eff2, List.isChain_singleton _⟩⟩
  · intro π hπ
    obtain ⟨hh, hl, hc⟩ := hπ
    rcases π with _ | ⟨A, _ | ⟨B, rest⟩⟩
    · simp at hh
    · simp at hh hl; exact absurd (hh ▸ hl) hSne
    · simp only [List.head?_cons, Option.some.injEq] at hh; subst hh
      rw [List.isChain_cons_cons] at hc
      have hB := step1 B hc.1; subst hB
      rcases rest with _ | ⟨C, rest'⟩
      · simp at hl; exact absurd hl hS1ne
      · rw [List.isChain_cons_cons] at hc
        have hC := step2 C hc.2.1; subst hC
        exact ⟨T, by simp [hT_hook], by simp⟩


private lemma interval_rev_eq (p : ℕ) :
    (interval (p + 1) (p + 12)).reverse =
      [p+12, p+11, p+10, p+9, p+8, p+7, p+6, p+5, p+4, p+3, p+2, p+1] := by
  unfold interval
  have hlen : p + 12 + 1 - (p + 1) = 12 := by omega
  rw [hlen]
  have h :
      List.range' (p + 1) 12 =
        [p+1, p+2, p+3, p+4, p+5, p+6, p+7, p+8, p+9, p+10, p+11, p+12] := by
    rw [List.range'_succ, List.range'_succ, List.range'_succ, List.range'_succ,
        List.range'_succ, List.range'_succ, List.range'_succ, List.range'_succ,
        List.range'_succ, List.range'_succ, List.range'_succ, List.range'_succ,
        List.range'_zero]
  rw [h]
  rfl

/-- Property 6(c): release opens the interval (two unique efficient flips). -/
theorem prop6_c (p : ℕ) (X Y : List ℕ)
    (hS : IsStack (hookG'' p ++ X ++ hookH'' p ++ Y)) :
    LeadsTo (hookG'' p ++ X ++ hookH'' p ++ Y)
      {X ++ (interval (p + 1) (p + 12)).reverse ++ Y} := by
  set S := hookG'' p ++ X ++ hookH'' p ++ Y with hSdef
  have hnd := stack_nodup S hS
  have hmem := memS S hS
  rw [hookG''_eq, hookH''_eq] at hSdef
  set S1 := [p+8, p+9, p+10, p+11, p+12] ++ X.reverse ++
      [p+7, p+6, p+5, p+4, p+3, p+2, p+1] ++ Y with hS1def
  set T := X ++ [p+12, p+11, p+10, p+9, p+8, p+7, p+6, p+5, p+4, p+3, p+2, p+1] ++ Y with hTdef
  have hT_hook : T = X ++ (interval (p + 1) (p + 12)).reverse ++ Y := by
    simp [hTdef, interval_rev_eq]
  have hSd : S = ([p+3, p+4, p+5, p+6, p+7] ++ X ++ [p+12, p+11, p+10, p+9, p+8]) ++
      (p + 2) :: ([p+1] ++ Y) := by
    rw [hSdef]; simp [List.append_assoc]
  have hpref_last :
      ([p+3, p+4, p+5, p+6, p+7] ++ X ++ [p+12, p+11, p+10, p+9, p+8]).getLast? =
        some (p + 8) := by
    rw [show [p+3, p+4, p+5, p+6, p+7] ++ X ++ [p+12, p+11, p+10, p+9, p+8] =
          ([p+3, p+4, p+5, p+6, p+7] ++ X ++ [p+12, p+11, p+10, p+9]) ++ [p + 8] by simp]
    exact getLast_snoc _ _
  have hS1eq : S1 =
      ([p+3, p+4, p+5, p+6, p+7] ++ X ++ [p+12, p+11, p+10, p+9, p+8]).reverse ++
        (p + 2) :: ([p+1] ++ Y) := by
    have h : [p+3, p+4, p+5, p+6, p+7] ++ X ++ [p+12, p+11, p+10, p+9, p+8] =
        ((((((([p+3] ++ [p+4]) ++ [p+5]) ++ [p+6]) ++ [p+7]) ++ X ++ [p+12]) ++ [p+11]) ++ [p+10]) ++ [p+9] ++ [p+8] := by
      simp [List.append_assoc]
    rw [hS1def, h]
    simp [List.reverse_append, List.reverse_cons, List.append_assoc]
  have eff1 : EfficientFlip S S1 := by
    have h := eff_of (p + 3) ([p+4, p+5, p+6, p+7] ++ X ++ [p+12, p+11, p+10, p+9, p+8]) (p + 8)
      (by simpa [List.cons_append, List.append_assoc] using hpref_last)
      (p + 2) ([p+1] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    simpa [hSd, hS1eq, List.cons_append] using h
  have hS1d : S1 = ([p+8, p+9, p+10, p+11, p+12] ++ X.reverse) ++
      (p + 7) :: ([p+6, p+5, p+4, p+3, p+2, p+1] ++ Y) := by
    simp [hS1def, List.append_assoc]
  have hTeq : T = ([p+8, p+9, p+10, p+11, p+12] ++ X.reverse).reverse ++
      (p + 7) :: ([p+6, p+5, p+4, p+3, p+2, p+1] ++ Y) := by
    simp [hTdef, List.reverse_append, List.reverse_cons, List.append_assoc]
  have eff2 : EfficientFlip S1 T := by
    cases hX : X with
    | nil =>
      have hL : ([p+8, p+9, p+10, p+11, p+12] ++ X.reverse).getLast? = some (p + 12) := by
        rw [hX]; change ([p+8, p+9, p+10, p+11] ++ [p+12]).getLast? = some (p + 12)
        exact getLast_snoc _ _
      have h := eff_of (p + 8) ([p+9, p+10, p+11, p+12] ++ X.reverse) (p + 12)
        (by simpa [List.cons_append, hX] using hL)
        (p + 7) ([p+6, p+5, p+4, p+3, p+2, p+1] ++ Y)
        (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
      simpa [hS1d, hTeq, List.cons_append, hX] using h
    | cons x X' =>
      have hnd0 : ([p+3, p+4, p+5, p+6, p+7] ++ X ++
          [p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y).Nodup := by
        simpa [hSdef] using hnd
      have hxX : x ∈ X := by simp [hX]
      have hx_ne_G : ∀ k, k ∈ ([p+3, p+4, p+5, p+6, p+7] : List ℕ) → x ≠ k := by
        intro k hk h0
        have hle := (List.nodup_iff_count_le_one.mp hnd0) x
        have : 2 ≤ List.count x ([p+3, p+4, p+5, p+6, p+7] ++ X ++
            [p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y) := by
          have hS' : [p+3, p+4, p+5, p+6, p+7] ++ X ++
              [p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y =
            [p+3, p+4, p+5, p+6, p+7] ++ (X ++ [p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y) := by
            simp [List.append_assoc]
          rw [hS', List.count_append]
          have g : 1 ≤ List.count x [p+3, p+4, p+5, p+6, p+7] := by
            subst h0; exact List.count_pos_iff.mpr hk
          have xx : 1 ≤ List.count x (X ++ [p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y) := by
            have : X ++ [p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y =
                X ++ ([p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y) := by simp [List.append_assoc]
            rw [this, List.count_append]
            have hxpos := List.count_pos_iff.mpr hxX
            omega
          omega
        omega
      have hx_ne6 : x ≠ p + 6 := hx_ne_G (p + 6) (by simp)
      have hx_ne8 : x ≠ p + 8 := fun h => x_ne_rel_H p X Y x hnd0 hxX (by simp [h])
      have hL : ([p+8, p+9, p+10, p+11, p+12] ++ X.reverse).getLast? = some x := by
        rw [hX, List.reverse_cons, ← List.append_assoc]; exact getLast_snoc _ _
      have h := eff_of (p + 8) ([p+9, p+10, p+11, p+12] ++ X.reverse) x
        (by simpa [List.cons_append] using hL)
        (p + 7) ([p+6, p+5, p+4, p+3, p+2, p+1] ++ Y)
        (by rw [pq_true_iff]; clear hL; omega) (by rw [pq_false_iff]; omega)
      simpa [hS1d, hTeq, List.cons_append] using h
  have hperm1 : S1.Perm S := by
    rw [hS1eq, hSd]; exact (List.reverse_perm _).append_right _
  have hlen1 : S1.length = S.length := hperm1.length_eq
  have hS1stack : IsStack S1 := by unfold IsStack; rw [hlen1]; exact hperm1.trans hS
  have hnd1 := stack_nodup S1 hS1stack
  have hSne : S ≠ identity S.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ S.length := by
      have := (hmem (p + 3) (by simp [hSdef])).2; omega
    have hid := identity_head _ hn0
    have hhd : S.head? = some (p + 3) := by simp [hSdef]
    rw [hid, hhd] at hh; injection hh with hh; omega
  have hS1ne : S1 ≠ identity S.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ S.length := by
      have := (hmem (p + 3) (by simp [hSdef])).2; omega
    have hid := identity_head _ hn0
    have hhd : S1.head? = some (p + 8) := by simp [hS1def]
    rw [hid, hhd] at hh; injection hh with hh; omega
  have step1 : ∀ B, EfficientFlip S B → B = S1 := by
    intro B hB
    rcases eff_char S B hB with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 3 := by
        have := congrArg List.head? (hSdef.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · -- a1+1 = b => b = p+4 (bad)
        subst h2
        have hSdAlt : S = [p+3] ++ (p + 4) ::
            ([p+5, p+6, p+7] ++ X ++ [p+12, p+11, p+10, p+9, p+8, p+2, p+1] ++ Y) := by
          simp [hSdef, List.append_assoc]
        obtain ⟨e1, -⟩ := split_uniq (p + 4) [p+3] _
          ((p + 3) :: A1) B' (hSdAlt ▸ hnd) (hSdAlt.symm.trans hSe)
        rw [e1] at hL; simp at hL; subst hL
        rw [pq_true_iff] at h1; omega
      · -- b+1 = a1 => b = p+2 (good)
        have hb : b = p + 2 := by omega
        subst hb
        obtain ⟨e1, e2⟩ := split_uniq (p + 2)
          ([p+3, p+4, p+5, p+6, p+7] ++ X ++ [p+12, p+11, p+10, p+9, p+8])
          ([p+1] ++ Y)
          ((p + 3) :: A1) B' (hSd ▸ hnd) (hSd.symm.trans hSe)
        rw [hBe, e1, e2, ← hS1eq]
    · exfalso
      rw [hSdef] at hh1; simp [ha1] at hh1
      have := (hmem (p + 12) (by simp [hSdef])).2; omega
  have step2 : ∀ C, EfficientFlip S1 C → C = T := by
    intro C hC
    rcases eff_char S1 C hC with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 8 := by
        have := congrArg List.head? (hS1def.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · -- a1+1 = b => b = p+9 (bad)
        subst h2
        have hSdAlt : S1 = [p+8] ++ (p + 9) ::
            ([p+10, p+11, p+12] ++ X.reverse ++ [p+7, p+6, p+5, p+4, p+3, p+2, p+1] ++ Y) := by
          simp [hS1def, List.append_assoc]
        obtain ⟨e1, -⟩ := split_uniq (p + 9) [p+8] _
          ((p + 8) :: A1) B' (hSdAlt ▸ hnd1) (hSdAlt.symm.trans hSe)
        rw [e1] at hL; simp at hL; subst hL
        rw [pq_true_iff] at h1; omega
      · -- b+1 = a1 => b = p+7 (good)
        have hb : b = p + 7 := by omega
        subst hb
        obtain ⟨e1, e2⟩ := split_uniq (p + 7)
          ([p+8, p+9, p+10, p+11, p+12] ++ X.reverse)
          ([p+6, p+5, p+4, p+3, p+2, p+1] ++ Y)
          ((p + 8) :: A1) B' (hS1d ▸ hnd1) (hS1d.symm.trans hSe)
        rw [hBe, e1, e2, ← hTeq]
    · exfalso
      rw [hS1def] at hh1; simp [ha1] at hh1
      have := (memS S1 hS1stack (p + 12) (by simp [hS1def])).2; omega
  refine ⟨?exist, ?unique⟩
  · intro T' hT'; rw [Set.mem_singleton_iff] at hT'; subst hT'
    refine ⟨[S, S1, T], rfl, ?_, ?_⟩
    · simpa [hT_hook] using (rfl : [S, S1, T].getLast? = some T)
    · exact List.isChain_cons_cons.mpr ⟨eff1,
        List.isChain_cons_cons.mpr ⟨eff2, List.isChain_singleton _⟩⟩
  · intro π hπ
    obtain ⟨hh, hl, hc⟩ := hπ
    rcases π with _ | ⟨A, _ | ⟨B, rest⟩⟩
    · simp at hh
    · simp at hh hl; exact absurd (hh ▸ hl) hSne
    · simp only [List.head?_cons, Option.some.injEq] at hh; subst hh
      rw [List.isChain_cons_cons] at hc
      have hB := step1 B hc.1; subst hB
      rcases rest with _ | ⟨C, rest'⟩
      · simp at hl; exact absurd hl hS1ne
      · rw [List.isChain_cons_cons] at hc
        have hC := step2 C hc.2.1; subst hC
        exact ⟨T, by simp [hT_hook], by simp⟩


end PancakeHard

theorem solution (p : ℕ) (X Y Z : List ℕ) :
    (PancakeHard.IsStack (PancakeHard.hookTake p :: X ++ PancakeHard.hookG p ++ Y ++ PancakeHard.hookH p ++ Z) →
      PancakeHard.LeadsTo (PancakeHard.hookTake p :: X ++ PancakeHard.hookG p ++ Y ++ PancakeHard.hookH p ++ Z)
        {Y ++ PancakeHard.hookG' p ++ X.reverse ++ PancakeHard.hookH' p ++ Z}) ∧
    (PancakeHard.IsStack (PancakeHard.hookPut p :: X ++ PancakeHard.hookG' p ++ Y.reverse ++ PancakeHard.hookH' p ++ Z) →
      PancakeHard.LeadsTo (PancakeHard.hookPut p :: X ++ PancakeHard.hookG' p ++ Y.reverse ++ PancakeHard.hookH' p ++ Z)
        {Y ++ PancakeHard.hookG'' p ++ X ++ PancakeHard.hookH'' p ++ Z}) ∧
    (PancakeHard.IsStack (PancakeHard.hookG'' p ++ X ++ PancakeHard.hookH'' p ++ Y) →
      PancakeHard.LeadsTo (PancakeHard.hookG'' p ++ X ++ PancakeHard.hookH'' p ++ Y)
        {X ++ (PancakeHard.interval (p + 1) (p + 12)).reverse ++ Y}) :=
  ⟨PancakeHard.prop6_a p X Y Z, PancakeHard.prop6_b p X Y Z, PancakeHard.prop6_c p X Y⟩
