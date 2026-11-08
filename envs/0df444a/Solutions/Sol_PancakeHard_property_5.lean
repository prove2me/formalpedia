-- Prove2me | solution 1 for PancakeHard.property_5
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-07T14:49:51.283189+00:00
-- url     : https://prove2.me/submissions/f7a343f9-78cc-41f4-a7ae-50757db4f9f5

import Mathlib
import Definitions.Def_PancakeHard_Lock

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
      obtain ⟨rfl, rfl⟩ := h; simp at hn
  | l :: L1, L2, [], B, hn, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; simp at hn
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

private lemma L_eq (p : ℕ) :
    lockSeq p = [p+1, p+2, p+9, p+8, p+5, p+6, p+4, p+3, p+11, p+12] := by
  simp [lockSeq, shift]

private lemma Lo_eq (p : ℕ) :
    lockOpen p = [p+1, p+2, p+3, p+4, p+6, p+5, p+8, p+9, p+10, p+11, p+12] := by
  simp [lockOpen, shift]

private lemma int_lock (p : ℕ) :
    interval (p + 1) (p + 12) =
      [p+1, p+2, p+3, p+4, p+5, p+6, p+7, p+8, p+9, p+10, p+11, p+12] := by
  unfold interval
  rw [show p + 12 + 1 - (p + 1) = 12 by omega]
  simp [List.range'_succ, List.range'_zero]

private lemma not_adj_of_mem_ne (a b : ℕ) (hne : a ≠ b) (hne2 : a ≠ b + 1) (hne3 : b ≠ a + 1) :
    pq (a, b) = true := by
  rw [pq_true_iff]; omega

/-- Deadlock helper: no efficient flip when the only candidate prefixes fail the adj tests. -/
private lemma deadlock_of_no_eff (S : List ℕ) (hne : S ≠ identity S.length)
    (H : ∀ S', ¬ EfficientFlip S S') : IsDeadlock S := ⟨hne, H⟩

/-- Characterize efficient flips of `a :: A ++ b :: B` when head is not `length`. -/
private lemma eff_flip_form {S S' : List ℕ} (h : EfficientFlip S S')
    (hn : ∀ a, S.head? = some a → a ≠ S.length) :
    ∃ a1 A1 aL b B, (a1 :: A1).getLast? = some aL ∧ S = (a1 :: A1) ++ b :: B ∧
      S' = (a1 :: A1).reverse ++ b :: B ∧ pq (aL, b) = true ∧ pq (a1, b) = false := by
  rcases eff_char S S' h with h | ⟨a1, hh, ha⟩
  · exact h
  · exact absurd ha (hn a1 hh)


/-! ### Nodup helpers -/

private lemma count_append_ge (x : ℕ) (A B : List ℕ) (hA : x ∈ A) (hB : x ∈ B) :
    2 ≤ List.count x (A ++ B) := by
  rw [List.count_append]
  have h1 := List.count_pos_iff.mpr hA
  have h2 := List.count_pos_iff.mpr hB
  omega

private lemma false_of_nodup_parts {x : ℕ} {A B : List ℕ}
    (hnd : (A ++ B).Nodup) (hA : x ∈ A) (hB : x ∈ B) : False := by
  have hle := (List.nodup_iff_count_le_one.mp hnd) x
  have hge := count_append_ge x A B hA hB
  omega

private lemma x_ne_lock_closed (p : ℕ) (X Y : List ℕ) (x z : ℕ)
    (hnd : ((p + 10) :: X ++ [p+1,p+2,p+9,p+8,p+5,p+6,p+4,p+3,p+11,p+12] ++ Y).Nodup)
    (hx : x ∈ X) (hz : z ∈ ([p+1,p+2,p+9,p+8,p+5,p+6,p+4,p+3,p+11,p+12] : List ℕ)) :
    x ≠ z := by
  intro h; subst h
  have hle := (List.nodup_iff_count_le_one.mp hnd) x
  have hx1 : x ∈ (p + 10) :: X := List.mem_cons_of_mem _ hx
  have hx2 : x ∈ [p+1,p+2,p+9,p+8,p+5,p+6,p+4,p+3,p+11,p+12] ++ Y :=
    List.mem_append_left _ hz
  rw [List.append_assoc] at hle
  have : 2 ≤ List.count x ((p + 10) :: X ++ ([p+1,p+2,p+9,p+8,p+5,p+6,p+4,p+3,p+11,p+12] ++ Y)) := by
    rw [List.count_append]
    have c1 := List.count_pos_iff.mpr hx1
    have c2 := List.count_pos_iff.mpr hx2
    omega
  omega

private lemma x_ne_lock_open (p : ℕ) (X Y : List ℕ) (x z : ℕ)
    (hnd : ((p + 7) :: X ++ [p+1,p+2,p+3,p+4,p+6,p+5,p+8,p+9,p+10,p+11,p+12] ++ Y).Nodup)
    (hx : x ∈ X) (hz : z ∈ ([p+1,p+2,p+3,p+4,p+6,p+5,p+8,p+9,p+10,p+11,p+12] : List ℕ)) :
    x ≠ z := by
  intro h; subst h
  have hle := (List.nodup_iff_count_le_one.mp hnd) x
  have hx1 : x ∈ (p + 7) :: X := List.mem_cons_of_mem _ hx
  have hx2 : x ∈ [p+1,p+2,p+3,p+4,p+6,p+5,p+8,p+9,p+10,p+11,p+12] ++ Y :=
    List.mem_append_left _ hz
  rw [List.append_assoc] at hle
  have : 2 ≤ List.count x ((p + 7) :: X ++ ([p+1,p+2,p+3,p+4,p+6,p+5,p+8,p+9,p+10,p+11,p+12] ++ Y)) := by
    rw [List.count_append]
    have c1 := List.count_pos_iff.mpr hx1
    have c2 := List.count_pos_iff.mpr hx2
    omega
  omega

private lemma getLast_snoc (A : List ℕ) (a : ℕ) : (A ++ [a]).getLast? = some a :=
  List.getLast?_concat

/-! ### Part (c) -/

private theorem prop5_c (p : ℕ) (X Y : List ℕ)
    (hS : IsStack (lockTest p :: X ++ lockSeq p ++ Y)) :
    IsDeadlock (lockTest p :: X ++ lockSeq p ++ Y) := by
  set S := lockTest p :: X ++ lockSeq p ++ Y with hSdef
  have hnd := stack_nodup S hS
  have hmem := memS S hS
  rw [show lockTest p = p + 7 by rfl, L_eq] at hSdef
  have hne : S ≠ identity S.length := by
    intro h
    have hh := congrArg List.head? h
    have hn0 : 1 ≤ S.length := by
      have hm := (hmem (p + 7) (by simp [hSdef])).2; omega
    have hid : (identity S.length).head? = some 1 := identity_head _ hn0
    have hhd : S.head? = some (p + 7) := by simp [hSdef]
    rw [hid, hhd] at hh; injection hh with hh; omega
  refine ⟨hne, ?_⟩
  intro S' hEff
  rcases eff_flip_form hEff (by
    intro a ha haLen
    have : a = p + 7 := by
      have hhd : S.head? = some (p + 7) := by simp [hSdef]
      have := hhd.symm.trans ha; injection this with this; exact this.symm
    have := (hmem (p + 12) (by simp [hSdef])).2; omega) with
    ⟨a1, A1, aL, b, B, hL, hSe, hBe, h1, h2⟩
  have ha1 : a1 = p + 7 := by
    have := congrArg List.head? (hSdef.symm.trans hSe); simpa [eq_comm] using this
  subst ha1; rw [pq_false_iff] at h2
  rcases h2 with h2 | h2
  · subst h2
    have hSd : S = ((p + 7) :: X ++ [p + 1, p + 2, p + 9]) ++ (p + 8) ::
        ([p + 5, p + 6, p + 4, p + 3, p + 11, p + 12] ++ Y) := by
      rw [hSdef]; simp [List.append_assoc]
    obtain ⟨e1, e2⟩ := split_uniq (p + 8) ((p + 7) :: X ++ [p + 1, p + 2, p + 9])
      ([p + 5, p + 6, p + 4, p + 3, p + 11, p + 12] ++ Y) ((p + 7) :: A1) B
      (hSd ▸ hnd) (hSd.symm.trans hSe)
    have hL' : ((p + 7) :: X ++ [p + 1, p + 2, p + 9]).getLast? = some (p + 9) := by
      rw [show (p + 7) :: X ++ [p + 1, p + 2, p + 9] =
            ((p + 7) :: X ++ [p + 1, p + 2]) ++ [p + 9] by simp]
      exact getLast_snoc _ _
    rw [e1, hL'] at hL; injection hL with hL; subst hL
    rw [pq_true_iff] at h1; omega
  · have hb : b = p + 6 := by omega
    subst hb
    have hSd : S = ((p + 7) :: X ++ [p + 1, p + 2, p + 9, p + 8, p + 5]) ++ (p + 6) ::
        ([p + 4, p + 3, p + 11, p + 12] ++ Y) := by
      rw [hSdef]; simp [List.append_assoc]
    obtain ⟨e1, -⟩ := split_uniq (p + 6) ((p + 7) :: X ++ [p + 1, p + 2, p + 9, p + 8, p + 5])
      ([p + 4, p + 3, p + 11, p + 12] ++ Y) ((p + 7) :: A1) B
      (hSd ▸ hnd) (hSd.symm.trans hSe)
    have hL' : ((p + 7) :: X ++ [p + 1, p + 2, p + 9, p + 8, p + 5]).getLast? = some (p + 5) := by
      rw [show (p + 7) :: X ++ [p + 1, p + 2, p + 9, p + 8, p + 5] =
            ((p + 7) :: X ++ [p + 1, p + 2, p + 9, p + 8]) ++ [p + 5] by simp]
      exact getLast_snoc _ _
    rw [e1, hL'] at hL; injection hL with hL; subst hL
    rw [pq_true_iff] at h1; omega

/-! ### Alt deadlocks -/

private theorem deadlock_alt_a (p : ℕ) (X Y : List ℕ)
    (hS : IsStack ((p + 10) :: X ++ [p+1,p+2,p+9,p+8,p+5,p+6,p+4,p+3,p+11,p+12] ++ Y)) :
    IsDeadlock ([p+2, p+1] ++ X.reverse ++
      [p+10, p+9, p+8, p+5, p+6, p+4, p+3, p+11, p+12] ++ Y) := by
  set B := [p+2, p+1] ++ X.reverse ++
      [p+10, p+9, p+8, p+5, p+6, p+4, p+3, p+11, p+12] ++ Y with hBdef
  set S0 := (p + 10) :: X ++ [p+1,p+2,p+9,p+8,p+5,p+6,p+4,p+3,p+11,p+12] ++ Y
  have hperm : B.Perm S0 := by
    have hB' : B = ((p + 10) :: X ++ [p + 1, p + 2]).reverse ++
        ([p+9, p+8, p+5, p+6, p+4, p+3, p+11, p+12] ++ Y) := by
      simp [hBdef, List.reverse_cons, List.reverse_append, List.append_assoc]
    have hS0' : S0 = ((p + 10) :: X ++ [p + 1, p + 2]) ++
        ([p+9, p+8, p+5, p+6, p+4, p+3, p+11, p+12] ++ Y) := by
      simp [S0, List.append_assoc]
    rw [hB', hS0']
    exact (List.reverse_perm _).append_right _
  have hBstack : IsStack B := by
    unfold IsStack; rw [hperm.length_eq]; exact hperm.trans hS
  have hnd := stack_nodup B hBstack
  have hmem := memS B hBstack
  have hne : B ≠ identity B.length := by
    intro h
    have hh := congrArg List.head? h
    have hn0 : 1 ≤ B.length := by
      have hm := (hmem (p + 2) (by simp [hBdef])).2; omega
    have hid : (identity B.length).head? = some 1 := identity_head _ hn0
    have hhd : B.head? = some (p + 2) := by simp [hBdef]
    rw [hid, hhd] at hh; injection hh with hh; omega
  refine ⟨hne, ?_⟩
  intro S' hEff
  rcases eff_flip_form hEff (by
    intro a ha haLen
    have : a = p + 2 := by
      have hhd : B.head? = some (p + 2) := by simp [hBdef]
      have := hhd.symm.trans ha; injection this with this; exact this.symm
    have := (hmem (p + 12) (by simp [hBdef])).2; omega) with
    ⟨a1, A1, aL, b, Brest, hL, hSe, hBe, h1, h2⟩
  have ha1 : a1 = p + 2 := by
    have := congrArg List.head? (hBdef.symm.trans hSe); simpa [eq_comm] using this
  subst ha1; rw [pq_false_iff] at h2
  rcases h2 with h2 | h2
  · subst h2
    have hBd : B = ([p+2, p+1] ++ X.reverse ++ [p+10, p+9, p+8, p+5, p+6, p+4]) ++
        (p + 3) :: ([p+11, p+12] ++ Y) := by rw [hBdef]; simp [List.append_assoc]
    obtain ⟨e1, -⟩ := split_uniq (p + 3)
      ([p+2, p+1] ++ X.reverse ++ [p+10, p+9, p+8, p+5, p+6, p+4])
      ([p+11, p+12] ++ Y) ((p + 2) :: A1) Brest (hBd ▸ hnd) (hBd.symm.trans hSe)
    have hL' : ([p+2, p+1] ++ X.reverse ++ [p+10, p+9, p+8, p+5, p+6, p+4]).getLast? =
        some (p + 4) := by
      rw [show [p+2, p+1] ++ X.reverse ++ [p+10, p+9, p+8, p+5, p+6, p+4] =
            ([p+2, p+1] ++ X.reverse ++ [p+10, p+9, p+8, p+5, p+6]) ++ [p + 4] by simp]
      exact getLast_snoc _ _
    rw [e1, hL'] at hL; injection hL with hL; subst hL
    rw [pq_true_iff] at h1; omega
  · have hb : b = p + 1 := by omega
    subst hb
    have hBd : B = [p + 2] ++ (p + 1) :: (X.reverse ++
        [p+10, p+9, p+8, p+5, p+6, p+4, p+3, p+11, p+12] ++ Y) := by
      rw [hBdef]; simp [List.append_assoc]
    obtain ⟨e1, -⟩ := split_uniq (p + 1) [p + 2] _ ((p + 2) :: A1) Brest
      (hBd ▸ hnd) (hBd.symm.trans hSe)
    rw [e1] at hL; simp at hL; subst hL
    rw [pq_true_iff] at h1; omega

private theorem deadlock_alt_b (p : ℕ) (X Y : List ℕ)
    (hS : IsStack ((p + 7) :: X ++
      [p+1,p+2,p+3,p+4,p+6,p+5,p+8,p+9,p+10,p+11,p+12] ++ Y)) :
    IsDeadlock ([p+4, p+3, p+2, p+1] ++ X.reverse ++
      [p+7, p+6, p+5, p+8, p+9, p+10, p+11, p+12] ++ Y) := by
  set B := [p+4, p+3, p+2, p+1] ++ X.reverse ++
      [p+7, p+6, p+5, p+8, p+9, p+10, p+11, p+12] ++ Y with hBdef
  set S0 := (p + 7) :: X ++
      [p+1,p+2,p+3,p+4,p+6,p+5,p+8,p+9,p+10,p+11,p+12] ++ Y
  have hperm : B.Perm S0 := by
    have hB' : B = ((p + 7) :: X ++ [p + 1, p + 2, p + 3, p + 4]).reverse ++
        ([p+6, p+5, p+8, p+9, p+10, p+11, p+12] ++ Y) := by
      simp [hBdef, List.reverse_cons, List.reverse_append, List.append_assoc]
    have hS0' : S0 = ((p + 7) :: X ++ [p + 1, p + 2, p + 3, p + 4]) ++
        ([p+6, p+5, p+8, p+9, p+10, p+11, p+12] ++ Y) := by
      simp [S0, List.append_assoc]
    rw [hB', hS0']
    exact (List.reverse_perm _).append_right _
  have hBstack : IsStack B := by
    unfold IsStack; rw [hperm.length_eq]; exact hperm.trans hS
  have hnd := stack_nodup B hBstack
  have hmem := memS B hBstack
  have hne : B ≠ identity B.length := by
    intro h
    have hh := congrArg List.head? h
    have hn0 : 1 ≤ B.length := by
      have hm := (hmem (p + 4) (by simp [hBdef])).2; omega
    have hid : (identity B.length).head? = some 1 := identity_head _ hn0
    have hhd : B.head? = some (p + 4) := by simp [hBdef]
    rw [hid, hhd] at hh; injection hh with hh; omega
  refine ⟨hne, ?_⟩
  intro S' hEff
  rcases eff_flip_form hEff (by
    intro a ha haLen
    have : a = p + 4 := by
      have hhd : B.head? = some (p + 4) := by simp [hBdef]
      have := hhd.symm.trans ha; injection this with this; exact this.symm
    have := (hmem (p + 12) (by simp [hBdef])).2; omega) with
    ⟨a1, A1, aL, b, Brest, hL, hSe, hBe, h1, h2⟩
  have ha1 : a1 = p + 4 := by
    have := congrArg List.head? (hBdef.symm.trans hSe); simpa [eq_comm] using this
  subst ha1; rw [pq_false_iff] at h2
  rcases h2 with h2 | h2
  · subst h2
    have hBd : B = ([p+4, p+3, p+2, p+1] ++ X.reverse ++ [p+7, p+6]) ++
        (p + 5) :: ([p+8, p+9, p+10, p+11, p+12] ++ Y) := by
      rw [hBdef]; simp [List.append_assoc]
    obtain ⟨e1, -⟩ := split_uniq (p + 5)
      ([p+4, p+3, p+2, p+1] ++ X.reverse ++ [p+7, p+6])
      ([p+8, p+9, p+10, p+11, p+12] ++ Y) ((p + 4) :: A1) Brest
      (hBd ▸ hnd) (hBd.symm.trans hSe)
    have hL' : ([p+4, p+3, p+2, p+1] ++ X.reverse ++ [p+7, p+6]).getLast? =
        some (p + 6) := by
      rw [show [p+4, p+3, p+2, p+1] ++ X.reverse ++ [p+7, p+6] =
            ([p+4, p+3, p+2, p+1] ++ X.reverse ++ [p+7]) ++ [p + 6] by simp]
      exact getLast_snoc _ _
    rw [e1, hL'] at hL; injection hL with hL; subst hL
    rw [pq_true_iff] at h1; omega
  · have hb : b = p + 3 := by omega
    subst hb
    have hBd : B = [p + 4] ++ (p + 3) :: ([p+2, p+1] ++ X.reverse ++
        [p+7, p+6, p+5, p+8, p+9, p+10, p+11, p+12] ++ Y) := by
      rw [hBdef]; simp [List.append_assoc]
    obtain ⟨e1, -⟩ := split_uniq (p + 3) [p + 4] _ ((p + 4) :: A1) Brest
      (hBd ▸ hnd) (hBd.symm.trans hSe)
    rw [e1] at hL; simp at hL; subst hL
    rw [pq_true_iff] at h1; omega


/-! ### Part (a): key opens lock -/

private theorem prop5_a (p : ℕ) (X Y : List ℕ)
    (hS : IsStack (lockKey p :: X ++ lockSeq p ++ Y)) :
    LeadsTo (lockKey p :: X ++ lockSeq p ++ Y) {X ++ lockOpen p ++ Y} := by
  set S := lockKey p :: X ++ lockSeq p ++ Y with hSdef
  have hnd := stack_nodup S hS
  have hmem := memS S hS
  rw [show lockKey p = p + 10 by rfl, L_eq] at hSdef
  set S1 := [p+3, p+4, p+6, p+5, p+8, p+9, p+2, p+1] ++ X.reverse ++
      [p+10, p+11, p+12] ++ Y with hS1def
  set S2 := [p+9, p+8, p+5, p+6, p+4, p+3, p+2, p+1] ++ X.reverse ++
      [p+10, p+11, p+12] ++ Y with hS2def
  set T := X ++ [p+1, p+2, p+3, p+4, p+6, p+5, p+8, p+9, p+10, p+11, p+12] ++ Y
  have hT_open : T = X ++ lockOpen p ++ Y := by rw [Lo_eq]
  have hSd : S = ((p + 10) :: X ++ [p+1, p+2, p+9, p+8, p+5, p+6, p+4, p+3]) ++
      (p + 11) :: ((p + 12) :: Y) := by
    rw [hSdef]; simp [List.append_assoc]
  have hpref1 :
      ((p + 10) :: X ++ [p+1, p+2, p+9, p+8, p+5, p+6, p+4, p+3]).getLast? = some (p + 3) := by
    rw [show (p + 10) :: X ++ [p+1, p+2, p+9, p+8, p+5, p+6, p+4, p+3] =
          ((p + 10) :: X ++ [p+1, p+2, p+9, p+8, p+5, p+6, p+4]) ++ [p + 3] by simp]
    exact getLast_snoc _ _
  have hS1eq : S1 =
      ((p + 10) :: X ++ [p+1, p+2, p+9, p+8, p+5, p+6, p+4, p+3]).reverse ++
        (p + 11) :: ((p + 12) :: Y) := by
    simp [hS1def, List.reverse_append, List.reverse_cons, List.append_assoc]
  have eff1 : EfficientFlip S S1 := by
    have h := eff_of (p + 10) (X ++ [p+1, p+2, p+9, p+8, p+5, p+6, p+4, p+3]) (p + 3)
      (by simpa [List.cons_append] using hpref1) (p + 11) ((p + 12) :: Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    simpa [hSd, hS1eq, List.cons_append] using h
  have hSd1 : S1 = [p+3, p+4, p+6, p+5, p+8, p+9] ++
      (p + 2) :: ([p+1] ++ X.reverse ++ [p+10, p+11, p+12] ++ Y) := by
    simp [hS1def, List.append_assoc]
  have eff2 : EfficientFlip S1 S2 := by
    have h := eff_of (p + 3) [p+4, p+6, p+5, p+8, p+9] (p + 9) (by simp) (p + 2)
      ([p+1] ++ X.reverse ++ [p+10, p+11, p+12] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    have hS2eq : S2 = [p+3, p+4, p+6, p+5, p+8, p+9].reverse ++
        (p + 2) :: ([p+1] ++ X.reverse ++ [p+10, p+11, p+12] ++ Y) := by
      simp [hS2def, List.append_assoc]
    simpa [hSd1, hS2eq] using h
  have hSd2 : S2 = ([p+9, p+8, p+5, p+6, p+4, p+3, p+2, p+1] ++ X.reverse) ++
      (p + 10) :: ([p+11, p+12] ++ Y) := by
    simp [hS2def, List.append_assoc]
  have hTrev : T = ([p+9, p+8, p+5, p+6, p+4, p+3, p+2, p+1] ++ X.reverse).reverse ++
      (p + 10) :: ([p+11, p+12] ++ Y) := by
    simp [T, List.reverse_append, List.reverse_cons, List.append_assoc]
  have eff3 : EfficientFlip S2 T := by
    cases hX : X with
    | nil =>
      have hL : ([p+9, p+8, p+5, p+6, p+4, p+3, p+2, p+1] ++ X.reverse).getLast? =
          some (p + 1) := by
        rw [hX]
        change ([p+9, p+8, p+5, p+6, p+4, p+3, p+2] ++ [p + 1]).getLast? = some (p + 1)
        exact getLast_snoc _ _
      have h := eff_of (p + 9) ([p+8, p+5, p+6, p+4, p+3, p+2, p+1] ++ X.reverse) (p + 1)
        (by simpa [List.cons_append, hX] using hL) (p + 10) ([p+11, p+12] ++ Y)
        (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
      simpa [hSd2, hTrev, List.cons_append] using h
    | cons x X' =>
      have hxX : x ∈ X := by simp [hX]
      have hnd0 : ((p + 10) :: X ++
          [p+1,p+2,p+9,p+8,p+5,p+6,p+4,p+3,p+11,p+12] ++ Y).Nodup := by
        simpa [hSdef] using hnd
      have hx_ne9 := x_ne_lock_closed p X Y x (p + 9) hnd0 hxX (by simp)
      have hx_ne11 := x_ne_lock_closed p X Y x (p + 11) hnd0 hxX (by simp)
      have hx_ne10 : x ≠ p + 10 := by
        intro h; subst h
        have hle := (List.nodup_iff_count_le_one.mp hnd0) (p + 10)
        rw [List.append_assoc, List.count_append, List.count_cons_self] at hle
        have hxpos := List.count_pos_iff.mpr (show (p + 10) ∈ X by simpa [hX] using hxX)
        omega
      have hL : ([p+9, p+8, p+5, p+6, p+4, p+3, p+2, p+1] ++ X.reverse).getLast? =
          some x := by
        rw [hX, List.reverse_cons, ← List.append_assoc]
        exact getLast_snoc _ _
      have h := eff_of (p + 9) ([p+8, p+5, p+6, p+4, p+3, p+2, p+1] ++ X.reverse) x
        (by
          have := hL
          simpa [List.cons_append] using this) (p + 10) ([p+11, p+12] ++ Y)
        (by rw [pq_true_iff]; clear hL; omega) (by rw [pq_false_iff]; omega)
      simpa [hSd2, hTrev, List.cons_append] using h
  have hperm1 : S1.Perm S := by rw [hS1eq, hSd]; exact (List.reverse_perm _).append_right _
  have hlenS : S1.length = S.length := hperm1.length_eq
  have hS1stack : IsStack S1 := by unfold IsStack; rw [hlenS]; exact hperm1.trans hS
  have hnd1 := stack_nodup S1 hS1stack
  have hperm2 : S2.Perm S1 := by
    have h2 : S2 = [p+3, p+4, p+6, p+5, p+8, p+9].reverse ++
        (p + 2) :: ([p+1] ++ X.reverse ++ [p+10, p+11, p+12] ++ Y) := by
      simp [hS2def, List.append_assoc]
    rw [hSd1, h2]; exact (List.reverse_perm _).append_right _
  have hS2stack : IsStack S2 := by
    unfold IsStack; rw [hperm2.length_eq, hlenS]; exact hperm2.trans (hperm1.trans hS)
  have hnd2 := stack_nodup S2 hS2stack
  have hSne : S ≠ identity S.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ S.length := by have := (hmem (p + 10) (by simp [hSdef])).2; omega
    have hid := identity_head _ hn0
    have hhd : S.head? = some (p + 10) := by simp [hSdef]
    rw [hid, hhd] at hh; injection hh with hh; omega
  have hS1ne : S1 ≠ identity S.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ S.length := by have := (hmem (p + 10) (by simp [hSdef])).2; omega
    have hid := identity_head _ hn0
    have hhd : S1.head? = some (p + 3) := by simp [hS1def]
    rw [hid, hhd] at hh; injection hh with hh; omega
  have hS2ne : S2 ≠ identity S.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ S.length := by have := (hmem (p + 10) (by simp [hSdef])).2; omega
    have hid := identity_head _ hn0
    have hhd : S2.head? = some (p + 9) := by simp [hS2def]
    rw [hid, hhd] at hh; injection hh with hh; omega
  refine ⟨?exist, ?unique⟩
  · intro T' hT'; rw [Set.mem_singleton_iff] at hT'; subst hT'
    refine ⟨[S, S1, S2, T], rfl, ?_, ?_⟩
    · simpa [hT_open] using (rfl : [S, S1, S2, T].getLast? = some T)
    · exact List.isChain_cons_cons.mpr ⟨eff1, List.isChain_cons_cons.mpr ⟨eff2,
        List.isChain_cons_cons.mpr ⟨eff3, List.isChain_singleton _⟩⟩⟩
  · intro π hπ
    obtain ⟨hh, hl, hc⟩ := hπ
    rcases π with _ | ⟨A, rest⟩
    · simp at hh
    · simp only [List.head?_cons, Option.some.injEq] at hh; subst hh
      rcases rest with _ | ⟨B, rest2⟩
      · simp at hl; exact absurd hl hSne
      · rw [List.isChain_cons_cons] at hc
        rcases eff_char S B hc.1 with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
        · have ha1' : a1 = p + 10 := by
            have := congrArg List.head? (hSdef.symm.trans hSe); simpa [eq_comm] using this
          subst ha1'; rw [pq_false_iff] at h2
          rcases h2 with h2 | h2
          · -- good first flip
            subst h2
            obtain ⟨e1, e2⟩ := split_uniq (p + 11)
              ((p + 10) :: X ++ [p+1, p+2, p+9, p+8, p+5, p+6, p+4, p+3])
              ((p + 12) :: Y) ((p + 10) :: A1) B' (hSd ▸ hnd) (hSd.symm.trans hSe)
            have hBeq : B = S1 := by rw [hBe, e1, e2, hS1eq]
            subst hBeq
            rcases rest2 with _ | ⟨C, rest3⟩
            · simp at hl; exact absurd hl hS1ne
            · rw [List.isChain_cons_cons] at hc
              rcases eff_char S1 C hc.2.1 with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
              · have ha1' : a1 = p + 3 := by
                  have := congrArg List.head? (hS1def.symm.trans hSe); simpa [eq_comm] using this
                subst ha1'; rw [pq_false_iff] at h2
                rcases h2 with h2 | h2
                · subst h2
                  have hSd_bad4 : S1 = [p+3] ++ (p + 4) ::
                      ([p+6, p+5, p+8, p+9, p+2, p+1] ++ X.reverse ++
                        [p+10, p+11, p+12] ++ Y) := by
                    simp [hS1def, List.append_assoc]
                  obtain ⟨e1, -⟩ := split_uniq (p + 4) [p+3] _
                    ((p + 3) :: A1) B' (hSd_bad4 ▸ hnd1) (hSd_bad4.symm.trans hSe)
                  rw [e1] at hL; simp at hL; subst hL
                  rw [pq_true_iff] at h1; omega
                · have hb : b = p + 2 := by omega
                  subst hb
                  obtain ⟨e1, e2⟩ := split_uniq (p + 2) [p+3, p+4, p+6, p+5, p+8, p+9]
                    ([p+1] ++ X.reverse ++ [p+10, p+11, p+12] ++ Y) ((p + 3) :: A1) B'
                    (hSd1 ▸ hnd1) (hSd1.symm.trans hSe)
                  have hCeq : C = S2 := by
                    rw [hBe, e1, e2]; simp [hS2def, List.append_assoc]
                  subst hCeq
                  rcases rest3 with _ | ⟨D, rest4⟩
                  · simp at hl; exact absurd hl hS2ne
                  · rw [List.isChain_cons_cons] at hc
                    rcases eff_char S2 D hc.2.2.1 with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
                    · have ha1' : a1 = p + 9 := by
                        have := congrArg List.head? (hS2def.symm.trans hSe); simpa [eq_comm] using this
                      subst ha1'; rw [pq_false_iff] at h2
                      rcases h2 with h2 | h2
                      · subst h2
                        obtain ⟨e1, e2⟩ := split_uniq (p + 10)
                          ([p+9, p+8, p+5, p+6, p+4, p+3, p+2, p+1] ++ X.reverse)
                          ([p+11, p+12] ++ Y) ((p + 9) :: A1) B'
                          (hSd2 ▸ hnd2) (hSd2.symm.trans hSe)
                        have hDeq : D = T := by rw [hBe, e1, e2, hTrev]
                        subst hDeq
                        exact ⟨X ++ lockOpen p ++ Y, by simp [hT_open], by simp [hT_open]⟩
                      · have hb : b = p + 8 := by omega
                        subst hb
                        have hSd_bad8 : S2 = [p+9] ++ (p + 8) ::
                            ([p+5, p+6, p+4, p+3, p+2, p+1] ++ X.reverse ++
                              [p+10, p+11, p+12] ++ Y) := by
                          simp [hS2def, List.append_assoc]
                        obtain ⟨e1, -⟩ := split_uniq (p + 8) [p+9] _
                          ((p + 9) :: A1) B' (hSd_bad8 ▸ hnd2) (hSd_bad8.symm.trans hSe)
                        rw [e1] at hL; simp at hL; subst hL
                        rw [pq_true_iff] at h1; omega
                    · exfalso
                      rw [hS2def] at hh1; simp [ha1] at hh1
                      have := (memS S2 hS2stack (p + 12) (by simp [hS2def])).2; omega
              · exfalso
                rw [hS1def] at hh1; simp [ha1] at hh1
                have := (memS S1 hS1stack (p + 12) (by simp [hS1def])).2; omega
          · -- alt first flip → deadlock
            have hb : b = p + 9 := by omega
            subst hb
            have hSdAlt : S = ((p + 10) :: X ++ [p+1, p+2]) ++ (p + 9) ::
                ([p+8, p+5, p+6, p+4, p+3, p+11, p+12] ++ Y) := by
              rw [hSdef]; simp [List.append_assoc]
            obtain ⟨e1, e2⟩ := split_uniq (p + 9) ((p + 10) :: X ++ [p+1, p+2])
              ([p+8, p+5, p+6, p+4, p+3, p+11, p+12] ++ Y) ((p + 10) :: A1) B'
              (hSdAlt ▸ hnd) (hSdAlt.symm.trans hSe)
            set Bdl := [p+2, p+1] ++ X.reverse ++
                [p+10, p+9, p+8, p+5, p+6, p+4, p+3, p+11, p+12] ++ Y
            have hBeq : B = Bdl := by
              rw [hBe, e1, e2]
              simp [Bdl, List.reverse_append, List.reverse_cons, List.append_assoc]
            subst hBeq
            have hDL := deadlock_alt_a p X Y (by simpa [hSdef] using hS)
            have hBne : Bdl ≠ identity S.length := by
              intro h; have hh := congrArg List.head? h
              have hn0 : 1 ≤ S.length := by have := (hmem (p + 10) (by simp [hSdef])).2; omega
              have hid := identity_head _ hn0
              have hhd : Bdl.head? = some (p + 2) := by simp [Bdl]
              rw [hid, hhd] at hh; injection hh with hh; omega
            rcases rest2 with _ | ⟨C, _⟩
            · simp at hl; exact absurd hl hBne
            · rw [List.isChain_cons_cons] at hc
              exact absurd hc.2.1 (hDL.2 C)
        · exfalso
          rw [hSdef] at hh1; simp [ha1] at hh1
          have := (hmem (p + 12) (by simp [hSdef])).2; omega

/-! ### Part (b): test opens open-lock to interval -/

private theorem prop5_b (p : ℕ) (X Y : List ℕ)
    (hS : IsStack (lockTest p :: X ++ lockOpen p ++ Y)) :
    LeadsTo (lockTest p :: X ++ lockOpen p ++ Y)
      {X ++ interval (p + 1) (p + 12) ++ Y} := by
  set S := lockTest p :: X ++ lockOpen p ++ Y with hSdef
  have hnd := stack_nodup S hS
  have hmem := memS S hS
  rw [show lockTest p = p + 7 by rfl, Lo_eq] at hSdef
  set S1 := [p+5, p+6, p+4, p+3, p+2, p+1] ++ X.reverse ++
      [p+7, p+8, p+9, p+10, p+11, p+12] ++ Y with hS1def
  set S2 := [p+6, p+5, p+4, p+3, p+2, p+1] ++ X.reverse ++
      [p+7, p+8, p+9, p+10, p+11, p+12] ++ Y with hS2def
  set T := X ++ [p+1, p+2, p+3, p+4, p+5, p+6, p+7, p+8, p+9, p+10, p+11, p+12] ++ Y
  have hT_int : T = X ++ interval (p + 1) (p + 12) ++ Y := by rw [int_lock]
  have hSd : S = ((p + 7) :: X ++ [p+1, p+2, p+3, p+4, p+6, p+5]) ++
      (p + 8) :: ([p+9, p+10, p+11, p+12] ++ Y) := by
    rw [hSdef]; simp [List.append_assoc]
  have hpref1 :
      ((p + 7) :: X ++ [p+1, p+2, p+3, p+4, p+6, p+5]).getLast? = some (p + 5) := by
    rw [show (p + 7) :: X ++ [p+1, p+2, p+3, p+4, p+6, p+5] =
          ((p + 7) :: X ++ [p+1, p+2, p+3, p+4, p+6]) ++ [p + 5] by simp]
    exact getLast_snoc _ _
  have hS1eq : S1 =
      ((p + 7) :: X ++ [p+1, p+2, p+3, p+4, p+6, p+5]).reverse ++
        (p + 8) :: ([p+9, p+10, p+11, p+12] ++ Y) := by
    simp [hS1def, List.reverse_append, List.reverse_cons, List.append_assoc]
  have eff1 : EfficientFlip S S1 := by
    have h := eff_of (p + 7) (X ++ [p+1, p+2, p+3, p+4, p+6, p+5]) (p + 5)
      (by simpa [List.cons_append] using hpref1) (p + 8) ([p+9, p+10, p+11, p+12] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    simpa [hSd, hS1eq, List.cons_append] using h
  have hSd1 : S1 = [p+5, p+6] ++
      (p + 4) :: ([p+3, p+2, p+1] ++ X.reverse ++ [p+7, p+8, p+9, p+10, p+11, p+12] ++ Y) := by
    simp [hS1def, List.append_assoc]
  have eff2 : EfficientFlip S1 S2 := by
    have h := eff_of (p + 5) [p+6] (p + 6) (by simp) (p + 4)
      ([p+3, p+2, p+1] ++ X.reverse ++ [p+7, p+8, p+9, p+10, p+11, p+12] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    have hS2eq : S2 = [p+5, p+6].reverse ++
        (p + 4) :: ([p+3, p+2, p+1] ++ X.reverse ++ [p+7, p+8, p+9, p+10, p+11, p+12] ++ Y) := by
      simp [hS2def, List.append_assoc]
    simpa [hSd1, hS2eq] using h
  have hSd2 : S2 = ([p+6, p+5, p+4, p+3, p+2, p+1] ++ X.reverse) ++
      (p + 7) :: ([p+8, p+9, p+10, p+11, p+12] ++ Y) := by
    simp [hS2def, List.append_assoc]
  have hTrev : T = ([p+6, p+5, p+4, p+3, p+2, p+1] ++ X.reverse).reverse ++
      (p + 7) :: ([p+8, p+9, p+10, p+11, p+12] ++ Y) := by
    simp [T, List.reverse_cons, List.append_assoc]
  have eff3 : EfficientFlip S2 T := by
    cases hX : X with
    | nil =>
      have hL : ([p+6, p+5, p+4, p+3, p+2, p+1] ++ X.reverse).getLast? =
          some (p + 1) := by
        rw [hX]
        change ([p+6, p+5, p+4, p+3, p+2] ++ [p + 1]).getLast? = some (p + 1)
        exact getLast_snoc _ _
      have h := eff_of (p + 6) ([p+5, p+4, p+3, p+2, p+1] ++ X.reverse) (p + 1)
        (by simpa [List.cons_append, hX] using hL) (p + 7) ([p+8, p+9, p+10, p+11, p+12] ++ Y)
        (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
      simpa [hSd2, hTrev, List.cons_append] using h
    | cons x X' =>
      have hxX : x ∈ X := by simp [hX]
      have hnd0 : ((p + 7) :: X ++
          [p+1,p+2,p+3,p+4,p+6,p+5,p+8,p+9,p+10,p+11,p+12] ++ Y).Nodup := by
        simpa [hSdef] using hnd
      have hx_ne6 := x_ne_lock_open p X Y x (p + 6) hnd0 hxX (by simp)
      have hx_ne8 := x_ne_lock_open p X Y x (p + 8) hnd0 hxX (by simp)
      have hx_ne7 : x ≠ p + 7 := by
        intro h; subst h
        have hle := (List.nodup_iff_count_le_one.mp hnd0) (p + 7)
        rw [List.append_assoc, List.count_append, List.count_cons_self] at hle
        have hxpos := List.count_pos_iff.mpr (show (p + 7) ∈ X by simpa [hX] using hxX)
        omega
      have hL : ([p+6, p+5, p+4, p+3, p+2, p+1] ++ X.reverse).getLast? =
          some x := by
        rw [hX, List.reverse_cons, ← List.append_assoc]
        exact getLast_snoc _ _
      have h := eff_of (p + 6) ([p+5, p+4, p+3, p+2, p+1] ++ X.reverse) x
        (by
          have := hL
          simpa [List.cons_append] using this) (p + 7) ([p+8, p+9, p+10, p+11, p+12] ++ Y)
        (by rw [pq_true_iff]; clear hL; omega) (by rw [pq_false_iff]; omega)
      simpa [hSd2, hTrev, List.cons_append] using h
  have hperm1 : S1.Perm S := by rw [hS1eq, hSd]; exact (List.reverse_perm _).append_right _
  have hlenS : S1.length = S.length := hperm1.length_eq
  have hS1stack : IsStack S1 := by unfold IsStack; rw [hlenS]; exact hperm1.trans hS
  have hnd1 := stack_nodup S1 hS1stack
  have hperm2 : S2.Perm S1 := by
    have h2 : S2 = [p+5, p+6].reverse ++
        (p + 4) :: ([p+3, p+2, p+1] ++ X.reverse ++ [p+7, p+8, p+9, p+10, p+11, p+12] ++ Y) := by
      simp [hS2def, List.append_assoc]
    rw [hSd1, h2]; exact (List.reverse_perm _).append_right _
  have hS2stack : IsStack S2 := by
    unfold IsStack; rw [hperm2.length_eq, hlenS]; exact hperm2.trans (hperm1.trans hS)
  have hnd2 := stack_nodup S2 hS2stack
  have hSne : S ≠ identity S.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ S.length := by have := (hmem (p + 7) (by simp [hSdef])).2; omega
    have hid := identity_head _ hn0
    have hhd : S.head? = some (p + 7) := by simp [hSdef]
    rw [hid, hhd] at hh; injection hh with hh; omega
  have hS1ne : S1 ≠ identity S.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ S.length := by have := (hmem (p + 7) (by simp [hSdef])).2; omega
    have hid := identity_head _ hn0
    have hhd : S1.head? = some (p + 5) := by simp [hS1def]
    rw [hid, hhd] at hh; injection hh with hh; omega
  have hS2ne : S2 ≠ identity S.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ S.length := by have := (hmem (p + 7) (by simp [hSdef])).2; omega
    have hid := identity_head _ hn0
    have hhd : S2.head? = some (p + 6) := by simp [hS2def]
    rw [hid, hhd] at hh; injection hh with hh; omega
  refine ⟨?exist, ?unique⟩
  · intro T' hT'; rw [Set.mem_singleton_iff] at hT'; subst hT'
    refine ⟨[S, S1, S2, T], rfl, ?_, ?_⟩
    · simpa [hT_int] using (rfl : [S, S1, S2, T].getLast? = some T)
    · exact List.isChain_cons_cons.mpr ⟨eff1, List.isChain_cons_cons.mpr ⟨eff2,
        List.isChain_cons_cons.mpr ⟨eff3, List.isChain_singleton _⟩⟩⟩
  · intro π hπ
    obtain ⟨hh, hl, hc⟩ := hπ
    rcases π with _ | ⟨A, rest⟩
    · simp at hh
    · simp only [List.head?_cons, Option.some.injEq] at hh; subst hh
      rcases rest with _ | ⟨B, rest2⟩
      · simp at hl; exact absurd hl hSne
      · rw [List.isChain_cons_cons] at hc
        rcases eff_char S B hc.1 with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
        · have ha1' : a1 = p + 7 := by
            have := congrArg List.head? (hSdef.symm.trans hSe); simpa [eq_comm] using this
          subst ha1'; rw [pq_false_iff] at h2
          rcases h2 with h2 | h2
          · -- good first flip
            subst h2
            obtain ⟨e1, e2⟩ := split_uniq (p + 8)
              ((p + 7) :: X ++ [p+1, p+2, p+3, p+4, p+6, p+5])
              ([p+9, p+10, p+11, p+12] ++ Y) ((p + 7) :: A1) B' (hSd ▸ hnd) (hSd.symm.trans hSe)
            have hBeq : B = S1 := by rw [hBe, e1, e2, hS1eq]
            subst hBeq
            rcases rest2 with _ | ⟨C, rest3⟩
            · simp at hl; exact absurd hl hS1ne
            · rw [List.isChain_cons_cons] at hc
              rcases eff_char S1 C hc.2.1 with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
              · have ha1' : a1 = p + 5 := by
                  have := congrArg List.head? (hS1def.symm.trans hSe); simpa [eq_comm] using this
                subst ha1'; rw [pq_false_iff] at h2
                rcases h2 with h2 | h2
                · subst h2
                  have hSd_bad6 : S1 = [p+5] ++ (p + 6) ::
                      ([p+4, p+3, p+2, p+1] ++ X.reverse ++
                        [p+7, p+8, p+9, p+10, p+11, p+12] ++ Y) := by
                    simp [hS1def, List.append_assoc]
                  obtain ⟨e1, -⟩ := split_uniq (p + 6) [p+5] _
                    ((p + 5) :: A1) B' (hSd_bad6 ▸ hnd1) (hSd_bad6.symm.trans hSe)
                  rw [e1] at hL; simp at hL; subst hL
                  rw [pq_true_iff] at h1; omega
                · have hb : b = p + 4 := by omega
                  subst hb
                  obtain ⟨e1, e2⟩ := split_uniq (p + 4) [p+5, p+6]
                    ([p+3, p+2, p+1] ++ X.reverse ++ [p+7, p+8, p+9, p+10, p+11, p+12] ++ Y)
                    ((p + 5) :: A1) B' (hSd1 ▸ hnd1) (hSd1.symm.trans hSe)
                  have hCeq : C = S2 := by
                    rw [hBe, e1, e2]; simp [hS2def, List.append_assoc]
                  subst hCeq
                  rcases rest3 with _ | ⟨D, rest4⟩
                  · simp at hl; exact absurd hl hS2ne
                  · rw [List.isChain_cons_cons] at hc
                    rcases eff_char S2 D hc.2.2.1 with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
                    · have ha1' : a1 = p + 6 := by
                        have := congrArg List.head? (hS2def.symm.trans hSe); simpa [eq_comm] using this
                      subst ha1'; rw [pq_false_iff] at h2
                      rcases h2 with h2 | h2
                      · subst h2
                        obtain ⟨e1, e2⟩ := split_uniq (p + 7)
                          ([p+6, p+5, p+4, p+3, p+2, p+1] ++ X.reverse)
                          ([p+8, p+9, p+10, p+11, p+12] ++ Y) ((p + 6) :: A1) B'
                          (hSd2 ▸ hnd2) (hSd2.symm.trans hSe)
                        have hDeq : D = T := by rw [hBe, e1, e2, hTrev]
                        subst hDeq
                        exact ⟨X ++ interval (p + 1) (p + 12) ++ Y, by simp [hT_int], by simp [hT_int]⟩
                      · have hb : b = p + 5 := by omega
                        subst hb
                        have hSd_bad5 : S2 = [p+6] ++ (p + 5) ::
                            ([p+4, p+3, p+2, p+1] ++ X.reverse ++
                              [p+7, p+8, p+9, p+10, p+11, p+12] ++ Y) := by
                          simp [hS2def, List.append_assoc]
                        obtain ⟨e1, -⟩ := split_uniq (p + 5) [p+6] _
                          ((p + 6) :: A1) B' (hSd_bad5 ▸ hnd2) (hSd_bad5.symm.trans hSe)
                        rw [e1] at hL; simp at hL; subst hL
                        rw [pq_true_iff] at h1; omega
                    · exfalso
                      rw [hS2def] at hh1; simp [ha1] at hh1
                      have := (memS S2 hS2stack (p + 12) (by simp [hS2def])).2; omega
              · exfalso
                rw [hS1def] at hh1; simp [ha1] at hh1
                have := (memS S1 hS1stack (p + 12) (by simp [hS1def])).2; omega
          · -- alt first flip → deadlock
            have hb : b = p + 6 := by omega
            subst hb
            have hSdAlt : S = ((p + 7) :: X ++ [p+1, p+2, p+3, p+4]) ++ (p + 6) ::
                ([p+5, p+8, p+9, p+10, p+11, p+12] ++ Y) := by
              rw [hSdef]; simp [List.append_assoc]
            obtain ⟨e1, e2⟩ := split_uniq (p + 6) ((p + 7) :: X ++ [p+1, p+2, p+3, p+4])
              ([p+5, p+8, p+9, p+10, p+11, p+12] ++ Y) ((p + 7) :: A1) B'
              (hSdAlt ▸ hnd) (hSdAlt.symm.trans hSe)
            set Bdl := [p+4, p+3, p+2, p+1] ++ X.reverse ++
                [p+7, p+6, p+5, p+8, p+9, p+10, p+11, p+12] ++ Y
            have hBeq : B = Bdl := by
              rw [hBe, e1, e2]
              simp [Bdl, List.reverse_append, List.reverse_cons, List.append_assoc]
            subst hBeq
            have hDL := deadlock_alt_b p X Y (by simpa [hSdef] using hS)
            have hBne : Bdl ≠ identity S.length := by
              intro h; have hh := congrArg List.head? h
              have hn0 : 1 ≤ S.length := by have := (hmem (p + 7) (by simp [hSdef])).2; omega
              have hid := identity_head _ hn0
              have hhd : Bdl.head? = some (p + 4) := by simp [Bdl]
              rw [hid, hhd] at hh; injection hh with hh; omega
            rcases rest2 with _ | ⟨C, _⟩
            · simp at hl; exact absurd hl hBne
            · rw [List.isChain_cons_cons] at hc
              exact absurd hc.2.1 (hDL.2 C)
        · exfalso
          rw [hSdef] at hh1; simp [ha1] at hh1
          have := (hmem (p + 12) (by simp [hSdef])).2; omega

end PancakeHard

theorem solution (p : ℕ) (X Y : List ℕ) :
    (PancakeHard.IsStack (PancakeHard.lockKey p :: X ++ PancakeHard.lockSeq p ++ Y) →
      PancakeHard.LeadsTo (PancakeHard.lockKey p :: X ++ PancakeHard.lockSeq p ++ Y)
        {X ++ PancakeHard.lockOpen p ++ Y}) ∧
    (PancakeHard.IsStack (PancakeHard.lockTest p :: X ++ PancakeHard.lockOpen p ++ Y) →
      PancakeHard.LeadsTo (PancakeHard.lockTest p :: X ++ PancakeHard.lockOpen p ++ Y)
        {X ++ PancakeHard.interval (p + 1) (p + 12) ++ Y}) ∧
    (PancakeHard.IsStack (PancakeHard.lockTest p :: X ++ PancakeHard.lockSeq p ++ Y) →
      PancakeHard.IsDeadlock (PancakeHard.lockTest p :: X ++ PancakeHard.lockSeq p ++ Y)) :=
  ⟨PancakeHard.prop5_a p X Y, PancakeHard.prop5_b p X Y, PancakeHard.prop5_c p X Y⟩
