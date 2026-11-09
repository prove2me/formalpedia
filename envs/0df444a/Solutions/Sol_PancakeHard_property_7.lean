-- Prove2me | solution 1 for PancakeHard.property_7
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-08T19:10:35.888638+00:00
-- url     : https://prove2.me/submissions/4fc5e7cd-6c7d-48ea-9aae-b2ddae11dc84

import Mathlib
import Definitions.Def_PancakeHard_Fork

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


private lemma getLast_snoc (A : List ℕ) (a : ℕ) : (A ++ [a]).getLast? = some a :=
  List.getLast?_concat


/-! ### Fork gadget equalities -/

private lemma forkE_eq (p : ℕ) : forkE p = [p+11, p+8, p+7, p+3] := by simp [forkE, shift]
private lemma forkF_eq (p : ℕ) :
    forkF p = [p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] := by
  simp [forkF, shift]
private lemma forkF1_eq (p : ℕ) :
    forkF1 p = [p+10, p+9, p+6, p+7, p+8, p+11, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] := by
  simp [forkF1, shift]
private lemma forkF2_eq (p : ℕ) :
    forkF2 p = [p+3, p+7, p+8, p+11, p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] := by
  simp [forkF2, shift]
private lemma int_fork (p : ℕ) :
    (interval (p + 1) (p + 15)).reverse =
      [p+15, p+14, p+13, p+12, p+11, p+10, p+9, p+8, p+7, p+6, p+5, p+4, p+3, p+2, p+1] := by
  unfold interval
  rw [show p + 15 + 1 - (p + 1) = 15 by omega]
  -- range' (p+1) 15 = [p+1,...,p+15]
  have h : List.range' (p + 1) 15 =
      [p+1, p+2, p+3, p+4, p+5, p+6, p+7, p+8, p+9, p+10, p+11, p+12, p+13, p+14, p+15] := by
    simp [List.range'_succ, List.range'_zero]
  rw [h]; simp

private lemma false_of_nodup_parts {x : ℕ} {A B : List ℕ}
    (hnd : (A ++ B).Nodup) (hA : x ∈ A) (hB : x ∈ B) : False := by
  have hle := (List.nodup_iff_count_le_one.mp hnd) x
  have : 2 ≤ List.count x (A ++ B) := by
    rw [List.count_append]
    have := List.count_pos_iff.mpr hA
    have := List.count_pos_iff.mpr hB
    omega
  omega

/-! ### Part (b): F¹ sorts to ★I -/

theorem prop7_b (p : ℕ) (Y : List ℕ)
    (hS : IsStack (forkF1 p ++ Y)) :
    LeadsTo (forkF1 p ++ Y) {(interval (p + 1) (p + 15)).reverse ++ Y} := by
  set S := forkF1 p ++ Y with hSdef
  have hnd := stack_nodup S hS
  have hmem := memS S hS
  rw [forkF1_eq] at hSdef
  set S1 := [p+8, p+7, p+6, p+9, p+10, p+11, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y
    with hS1def
  set S2 := [p+6, p+7, p+8, p+9, p+10, p+11, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y
    with hS2def
  set T := [p+15, p+14, p+13, p+12, p+11, p+10, p+9, p+8, p+7, p+6, p+5, p+4, p+3, p+2, p+1] ++ Y
    with hTdef
  have hT_int : T = (interval (p + 1) (p + 15)).reverse ++ Y := by rw [hTdef, int_fork]
  -- flip 5: through p+8 join p+11
  have hSd : S = [p+10, p+9, p+6, p+7, p+8] ++ (p + 11) ::
      ([p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by
    rw [hSdef]; simp [List.append_assoc]
  have eff1 : EfficientFlip S S1 := by
    have h := eff_of (p + 10) [p+9, p+6, p+7, p+8] (p + 8) (by simp) (p + 11)
      ([p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    have hS1eq : S1 = [p+10, p+9, p+6, p+7, p+8].reverse ++ (p + 11) ::
        ([p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by
      simp [hS1def, List.append_assoc]
    simpa [hSd, hS1eq] using h
  -- flip 3: through p+6 join p+9
  have hS1d : S1 = [p+8, p+7, p+6] ++ (p + 9) ::
      ([p+10, p+11, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by
    simp [hS1def, List.append_assoc]
  have eff2 : EfficientFlip S1 S2 := by
    have h := eff_of (p + 8) [p+7, p+6] (p + 6) (by simp) (p + 9)
      ([p+10, p+11, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    have hS2eq : S2 = [p+8, p+7, p+6].reverse ++ (p + 9) ::
        ([p+10, p+11, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by
      simp [hS2def, List.append_assoc]
    simpa [hS1d, hS2eq] using h
  -- flip 10: through p+15 join p+5
  have hS2d : S2 = [p+6, p+7, p+8, p+9, p+10, p+11, p+12, p+13, p+14, p+15] ++
      (p + 5) :: ([p+4, p+3, p+2, p+1] ++ Y) := by
    simp [hS2def, List.append_assoc]
  have hTeq : T = [p+6, p+7, p+8, p+9, p+10, p+11, p+12, p+13, p+14, p+15].reverse ++
      (p + 5) :: ([p+4, p+3, p+2, p+1] ++ Y) := by
    simp [hTdef, List.append_assoc]
  have eff3 : EfficientFlip S2 T := by
    have h := eff_of (p + 6) [p+7, p+8, p+9, p+10, p+11, p+12, p+13, p+14, p+15] (p + 15)
      (by simp) (p + 5) ([p+4, p+3, p+2, p+1] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    simpa [hS2d, hTeq] using h
  have hperm1 : S1.Perm S := by
    have hS1eq : S1 = [p+10, p+9, p+6, p+7, p+8].reverse ++ (p + 11) ::
        ([p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by
      simp [hS1def, List.append_assoc]
    rw [hS1eq, hSd]; exact (List.reverse_perm _).append_right _
  have hlen1 : S1.length = S.length := hperm1.length_eq
  have hS1stack : IsStack S1 := by unfold IsStack; rw [hlen1]; exact hperm1.trans hS
  have hnd1 := stack_nodup S1 hS1stack
  have hperm2 : S2.Perm S1 := by
    have h1 : S1 = [p+8, p+7, p+6] ++ (p + 9) ::
        ([p+10, p+11, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := hS1d
    have h2 : S2 = [p+8, p+7, p+6].reverse ++ (p + 9) ::
        ([p+10, p+11, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by
      simp [hS2def, List.append_assoc]
    rw [h1, h2]; exact (List.reverse_perm _).append_right _
  have hS2stack : IsStack S2 := by
    unfold IsStack; rw [hperm2.length_eq, hlen1]; exact hperm2.trans (hperm1.trans hS)
  have hnd2 := stack_nodup S2 hS2stack
  have hSne : S ≠ identity S.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ S.length := by have := (hmem (p + 15) (by simp [hSdef])).2; omega
    have hid := identity_head _ hn0
    have hhd : S.head? = some (p + 10) := by simp [hSdef]
    rw [hid, hhd] at hh; injection hh with hh; omega
  have hS1ne : S1 ≠ identity S.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ S.length := by have := (hmem (p + 15) (by simp [hSdef])).2; omega
    have hid := identity_head _ hn0
    have hhd : S1.head? = some (p + 8) := by simp [hS1def]
    rw [hid, hhd] at hh; injection hh with hh; omega
  have hS2ne : S2 ≠ identity S.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ S.length := by have := (hmem (p + 15) (by simp [hSdef])).2; omega
    have hid := identity_head _ hn0
    have hhd : S2.head? = some (p + 6) := by simp [hS2def]
    rw [hid, hhd] at hh; injection hh with hh; omega
  -- uniqueness of each flip
  have step1 : ∀ B, EfficientFlip S B → B = S1 := by
    intro B hB
    rcases eff_char S B hB with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 10 := by
        have := congrArg List.head? (hSdef.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · subst h2
        -- b = p+11 only good join
        obtain ⟨e1, e2⟩ := split_uniq (p + 11) [p+10, p+9, p+6, p+7, p+8]
          ([p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) ((p + 10) :: A1) B'
          (hSd ▸ hnd) (hSd.symm.trans hSe)
        rw [hBe, e1, e2]
        simp [hS1def, List.append_assoc]
      · -- b = p+9
        have hb : b = p + 9 := by omega
        subst hb
        have hSd' : S = [p+10] ++ (p + 9) ::
            ([p+6, p+7, p+8, p+11, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by
          rw [hSdef]; simp [List.append_assoc]
        obtain ⟨e1, -⟩ := split_uniq (p + 9) [p+10] _ ((p + 10) :: A1) B'
          (hSd' ▸ hnd) (hSd'.symm.trans hSe)
        rw [e1] at hL; simp at hL; subst hL
        rw [pq_true_iff] at h1; omega
    · exfalso
      rw [hSdef] at hh1; simp [ha1] at hh1
      have := (hmem (p + 15) (by simp [hSdef])).2; omega
  have step2 : ∀ C, EfficientFlip S1 C → C = S2 := by
    intro C hC
    rcases eff_char S1 C hC with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 8 := by
        have := congrArg List.head? (hS1def.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · subst h2
        obtain ⟨e1, e2⟩ := split_uniq (p + 9) [p+8, p+7, p+6]
          ([p+10, p+11, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y)
          ((p + 8) :: A1) B' (hS1d ▸ hnd1) (hS1d.symm.trans hSe)
        rw [hBe, e1, e2]; simp [hS2def, List.append_assoc]
      · have hb : b = p + 7 := by omega
        subst hb
        have hSd' : S1 = [p+8] ++ (p + 7) ::
            ([p+6, p+9, p+10, p+11, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by
          simp [hS1def, List.append_assoc]
        obtain ⟨e1, -⟩ := split_uniq (p + 7) [p+8] _ ((p + 8) :: A1) B'
          (hSd' ▸ hnd1) (hSd'.symm.trans hSe)
        rw [e1] at hL; simp at hL; subst hL
        rw [pq_true_iff] at h1; omega
    · exfalso
      rw [hS1def] at hh1; simp [ha1] at hh1
      have := (memS S1 hS1stack (p + 15) (by simp [hS1def])).2; omega
  have step3 : ∀ D, EfficientFlip S2 D → D = T := by
    intro D hD
    rcases eff_char S2 D hD with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 6 := by
        have := congrArg List.head? (hS2def.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · -- a1+1 = b => b = p+7 (bad short flip)
        subst h2
        have hSd' : S2 = [p+6] ++ (p + 7) ::
            ([p+8, p+9, p+10, p+11, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by
          simp [hS2def]
        obtain ⟨e1, -⟩ := split_uniq (p + 7) [p+6] _ ((p + 6) :: A1) B'
          (hSd' ▸ hnd2) (hSd'.symm.trans hSe)
        rw [e1] at hL; simp at hL; subst hL
        rw [pq_true_iff] at h1; omega
      · -- b+1 = a1 => b = p+5 (good)
        have hb : b = p + 5 := by omega
        subst hb
        obtain ⟨e1, e2⟩ := split_uniq (p + 5)
          [p+6, p+7, p+8, p+9, p+10, p+11, p+12, p+13, p+14, p+15]
          ([p+4, p+3, p+2, p+1] ++ Y) ((p + 6) :: A1) B'
          (hS2d ▸ hnd2) (hS2d.symm.trans hSe)
        rw [hBe, e1, e2, hTeq]
    · exfalso
      rw [hS2def] at hh1; simp [ha1] at hh1
      have := (memS S2 hS2stack (p + 15) (by simp [hS2def])).2; omega
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
      · have hB : B = S1 := step1 B (List.isChain_cons_cons.mp hc).1
        subst hB
        rcases rest2 with _ | ⟨C, rest3⟩
        · simp at hl; exact absurd hl hS1ne
        · have hC : C = S2 := step2 C (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hc).2).1
          subst hC
          rcases rest3 with _ | ⟨D, rest4⟩
          · simp at hl; exact absurd hl hS2ne
          · have hD : D = T := step3 D (by
              have hc' := (List.isChain_cons_cons.mp hc).2
              have hc'' := (List.isChain_cons_cons.mp hc').2
              exact (List.isChain_cons_cons.mp hc'').1)
            subst hD
            exact ⟨(interval (p + 1) (p + 15)).reverse ++ Y, by simp [hT_int], by simp [hT_int]⟩

/-! ### Part (c) WIP: deadlock + existence path (uniqueness next) -/

private theorem deadlock_alt_f2 (p : ℕ) (Y : List ℕ)
    (hS : IsStack (forkF2 p ++ Y)) :
    IsDeadlock ([p+13, p+12, p+6, p+9, p+10, p+11, p+8, p+7, p+3, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
  set B := [p+13, p+12, p+6, p+9, p+10, p+11, p+8, p+7, p+3, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y
    with hBdef
  have hperm : B.Perm (forkF2 p ++ Y) := by
    have hB' : B = ([p+3, p+7, p+8, p+11, p+10, p+9, p+6, p+12, p+13]).reverse ++
        ([p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by simp [hBdef]
    have hS0' : forkF2 p ++ Y = [p+3, p+7, p+8, p+11, p+10, p+9, p+6, p+12, p+13] ++
        ([p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by simp [forkF2_eq]
    rw [hB', hS0']; exact (List.reverse_perm _).append_right _
  have hBstack : IsStack B := by unfold IsStack; rw [hperm.length_eq]; exact hperm.trans hS
  have hnd := stack_nodup B hBstack
  have hmem := memS B hBstack
  have hne : B ≠ identity B.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ B.length := by have := (hmem (p + 15) (by simp [hBdef])).2; omega
    have hid := identity_head _ hn0
    have hhd : B.head? = some (p + 13) := by simp [hBdef]
    rw [hid, hhd] at hh; injection hh with hh; omega
  refine ⟨hne, ?_⟩
  intro S' hEff
  rcases eff_flip_form hEff (by
    intro a ha haLen
    have : a = p + 13 := by
      have hhd : B.head? = some (p + 13) := by simp [hBdef]
      have := hhd.symm.trans ha; injection this with this; exact this.symm
    have := (hmem (p + 15) (by simp [hBdef])).2; omega) with
    ⟨a1, A1, aL, b, Brest, hL, hSe, hBe, h1, h2⟩
  have ha1 : a1 = p + 13 := by
    have := congrArg List.head? (hBdef.symm.trans hSe); simpa [eq_comm] using this
  subst ha1; rw [pq_false_iff] at h2
  rcases h2 with h2 | h2
  · subst h2
    have hBd : B = [p+13, p+12, p+6, p+9, p+10, p+11, p+8, p+7, p+3, p+4, p+5, p+15] ++
        (p + 14) :: ([p+2, p+1] ++ Y) := by rw [hBdef]; simp
    obtain ⟨e1, -⟩ := split_uniq (p + 14)
      [p+13, p+12, p+6, p+9, p+10, p+11, p+8, p+7, p+3, p+4, p+5, p+15]
      ([p+2, p+1] ++ Y) ((p + 13) :: A1) Brest (hBd ▸ hnd) (hBd.symm.trans hSe)
    have hL' : ([p+13, p+12, p+6, p+9, p+10, p+11, p+8, p+7, p+3, p+4, p+5, p+15]).getLast? =
        some (p + 15) := by simp
    rw [e1, hL'] at hL; injection hL with hL; subst hL
    rw [pq_true_iff] at h1; omega
  · have hb : b = p + 12 := by omega
    subst hb
    have hBd : B = [p+13] ++ (p + 12) ::
        ([p+6, p+9, p+10, p+11, p+8, p+7, p+3, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
      rw [hBdef]; simp
    obtain ⟨e1, -⟩ := split_uniq (p + 12) [p+13] _ ((p + 13) :: A1) Brest
      (hBd ▸ hnd) (hBd.symm.trans hSe)
    rw [e1] at hL; simp at hL; subst hL
    rw [pq_true_iff] at h1; omega

theorem prop7_c (p : ℕ) (Y : List ℕ)
    (hS : IsStack (forkF2 p ++ Y)) :
    LeadsTo (forkF2 p ++ Y) {(interval (p + 1) (p + 15)).reverse ++ Y} := by
  set S := forkF2 p ++ Y with hSdef
  have hnd := stack_nodup S hS
  have hmem := memS S hS
  rw [forkF2_eq] at hSdef
  set S1 := [p+14, p+15, p+5, p+4, p+13, p+12, p+6, p+9, p+10, p+11, p+8, p+7, p+3, p+2, p+1] ++ Y with hS1def
  set S2 := [p+4, p+5, p+15, p+14, p+13, p+12, p+6, p+9, p+10, p+11, p+8, p+7, p+3, p+2, p+1] ++ Y with hS2def
  set S3 := [p+7, p+8, p+11, p+10, p+9, p+6, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y with hS3def
  set S4 := [p+9, p+10, p+11, p+8, p+7, p+6, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y with hS4def
  set S5 := [p+11, p+10, p+9, p+8, p+7, p+6, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y with hS5def
  set S6 := [p+6, p+7, p+8, p+9, p+10, p+11, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y with hS6def
  set T := [p+15, p+14, p+13, p+12, p+11, p+10, p+9, p+8, p+7, p+6, p+5, p+4, p+3, p+2, p+1] ++ Y with hTdef
  have hT_int : T = (interval (p + 1) (p + 15)).reverse ++ Y := by rw [hTdef, int_fork]
  have hSd : S = [p+3, p+7, p+8, p+11, p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14] ++
      (p + 2) :: ([p+1] ++ Y) := by rw [hSdef]; simp
  have eff1 : EfficientFlip S S1 := by
    have h := eff_of (p + 3) [p+7, p+8, p+11, p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14]
      (p + 14) (by simp) (p + 2) ([p+1] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    have hS1eq : S1 = [p+3, p+7, p+8, p+11, p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14].reverse ++
        (p + 2) :: ([p+1] ++ Y) := by simp [hS1def]
    simpa [hSd, hS1eq] using h
  have hS1d : S1 = [p+14, p+15, p+5, p+4] ++ (p + 13) ::
      ([p+12, p+6, p+9, p+10, p+11, p+8, p+7, p+3, p+2, p+1] ++ Y) := by simp [hS1def]
  have eff2 : EfficientFlip S1 S2 := by
    have h := eff_of (p + 14) [p+15, p+5, p+4] (p + 4) (by simp) (p + 13)
      ([p+12, p+6, p+9, p+10, p+11, p+8, p+7, p+3, p+2, p+1] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    have hS2eq : S2 = [p+14, p+15, p+5, p+4].reverse ++ (p + 13) ::
        ([p+12, p+6, p+9, p+10, p+11, p+8, p+7, p+3, p+2, p+1] ++ Y) := by simp [hS2def]
    simpa [hS1d, hS2eq] using h
  have hS2d : S2 = [p+4, p+5, p+15, p+14, p+13, p+12, p+6, p+9, p+10, p+11, p+8, p+7] ++
      (p + 3) :: ([p+2, p+1] ++ Y) := by simp [hS2def]
  have eff3 : EfficientFlip S2 S3 := by
    have h := eff_of (p + 4) [p+5, p+15, p+14, p+13, p+12, p+6, p+9, p+10, p+11, p+8, p+7]
      (p + 7) (by simp) (p + 3) ([p+2, p+1] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    have hS3eq : S3 = [p+4, p+5, p+15, p+14, p+13, p+12, p+6, p+9, p+10, p+11, p+8, p+7].reverse ++
        (p + 3) :: ([p+2, p+1] ++ Y) := by simp [hS3def]
    simpa [hS2d, hS3eq] using h
  have hS3d : S3 = [p+7, p+8, p+11, p+10, p+9] ++ (p + 6) ::
      ([p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by simp [hS3def]
  have eff4 : EfficientFlip S3 S4 := by
    have h := eff_of (p + 7) [p+8, p+11, p+10, p+9] (p + 9) (by simp) (p + 6)
      ([p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    have hS4eq : S4 = [p+7, p+8, p+11, p+10, p+9].reverse ++ (p + 6) ::
        ([p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by simp [hS4def]
    simpa [hS3d, hS4eq] using h
  have hS4d : S4 = [p+9, p+10, p+11] ++ (p + 8) ::
      ([p+7, p+6, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by simp [hS4def]
  have eff5 : EfficientFlip S4 S5 := by
    have h := eff_of (p + 9) [p+10, p+11] (p + 11) (by simp) (p + 8)
      ([p+7, p+6, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    have hS5eq : S5 = [p+9, p+10, p+11].reverse ++ (p + 8) ::
        ([p+7, p+6, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by simp [hS5def]
    simpa [hS4d, hS5eq] using h
  have hS5d : S5 = [p+11, p+10, p+9, p+8, p+7, p+6] ++ (p + 12) ::
      ([p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by simp [hS5def]
  have eff6 : EfficientFlip S5 S6 := by
    have h := eff_of (p + 11) [p+10, p+9, p+8, p+7, p+6] (p + 6) (by simp) (p + 12)
      ([p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    have hS6eq : S6 = [p+11, p+10, p+9, p+8, p+7, p+6].reverse ++ (p + 12) ::
        ([p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by simp [hS6def]
    simpa [hS5d, hS6eq] using h
  have hS6d : S6 = [p+6, p+7, p+8, p+9, p+10, p+11, p+12, p+13, p+14, p+15] ++
      (p + 5) :: ([p+4, p+3, p+2, p+1] ++ Y) := by simp [hS6def]
  have hTeq : T = [p+6, p+7, p+8, p+9, p+10, p+11, p+12, p+13, p+14, p+15].reverse ++
      (p + 5) :: ([p+4, p+3, p+2, p+1] ++ Y) := by simp [hTdef]
  have eff7 : EfficientFlip S6 T := by
    have h := eff_of (p + 6) [p+7, p+8, p+9, p+10, p+11, p+12, p+13, p+14, p+15] (p + 15)
      (by simp) (p + 5) ([p+4, p+3, p+2, p+1] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    simpa [hS6d, hTeq] using h
  have hperm1 : S1.Perm S := by
    have hS1eq : S1 = [p+3, p+7, p+8, p+11, p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14].reverse ++
        (p + 2) :: ([p+1] ++ Y) := by simp [hS1def]
    rw [hS1eq, hSd]; exact (List.reverse_perm _).append_right _
  have hS1stack : IsStack S1 := by unfold IsStack; rw [hperm1.length_eq]; exact hperm1.trans hS
  have hnd1 := stack_nodup S1 hS1stack
  have hperm2 : S2.Perm S1 := by
    have h2 : S2 = [p+14, p+15, p+5, p+4].reverse ++ (p + 13) ::
        ([p+12, p+6, p+9, p+10, p+11, p+8, p+7, p+3, p+2, p+1] ++ Y) := by simp [hS2def]
    rw [hS1d, h2]; exact (List.reverse_perm _).append_right _
  have hS2stack : IsStack S2 := by
    unfold IsStack; rw [hperm2.length_eq, hperm1.length_eq]; exact hperm2.trans (hperm1.trans hS)
  have hnd2 := stack_nodup S2 hS2stack
  have hperm3 : S3.Perm S2 := by
    have h3 : S3 = [p+4, p+5, p+15, p+14, p+13, p+12, p+6, p+9, p+10, p+11, p+8, p+7].reverse ++
        (p + 3) :: ([p+2, p+1] ++ Y) := by simp [hS3def]
    rw [hS2d, h3]; exact (List.reverse_perm _).append_right _
  have hS3stack : IsStack S3 := by
    unfold IsStack; rw [hperm3.length_eq, hperm2.length_eq, hperm1.length_eq]
    exact hperm3.trans (hperm2.trans (hperm1.trans hS))
  have hnd3 := stack_nodup S3 hS3stack
  have hperm4 : S4.Perm S3 := by
    have h4 : S4 = [p+7, p+8, p+11, p+10, p+9].reverse ++ (p + 6) ::
        ([p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by simp [hS4def]
    rw [hS3d, h4]; exact (List.reverse_perm _).append_right _
  have hS4stack : IsStack S4 := by
    unfold IsStack; rw [hperm4.length_eq, hperm3.length_eq, hperm2.length_eq, hperm1.length_eq]
    exact hperm4.trans (hperm3.trans (hperm2.trans (hperm1.trans hS)))
  have hnd4 := stack_nodup S4 hS4stack
  have hperm5 : S5.Perm S4 := by
    have h5 : S5 = [p+9, p+10, p+11].reverse ++ (p + 8) ::
        ([p+7, p+6, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by simp [hS5def]
    rw [hS4d, h5]; exact (List.reverse_perm _).append_right _
  have hS5stack : IsStack S5 := by
    unfold IsStack
    rw [hperm5.length_eq, hperm4.length_eq, hperm3.length_eq, hperm2.length_eq, hperm1.length_eq]
    exact hperm5.trans (hperm4.trans (hperm3.trans (hperm2.trans (hperm1.trans hS))))
  have hnd5 := stack_nodup S5 hS5stack
  have hperm6 : S6.Perm S5 := by
    have h6 : S6 = [p+11, p+10, p+9, p+8, p+7, p+6].reverse ++ (p + 12) ::
        ([p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by simp [hS6def]
    rw [hS5d, h6]; exact (List.reverse_perm _).append_right _
  have hS6stack : IsStack S6 := by
    unfold IsStack
    rw [hperm6.length_eq, hperm5.length_eq, hperm4.length_eq, hperm3.length_eq, hperm2.length_eq,
      hperm1.length_eq]
    exact hperm6.trans (hperm5.trans (hperm4.trans (hperm3.trans (hperm2.trans (hperm1.trans hS)))))
  have hnd6 := stack_nodup S6 hS6stack
  have ne_head (U : List ℕ) (u : ℕ) (hU : U.head? = some u) (hu : 1 < u ∨ u = 0) :
      U ≠ identity S.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ S.length := by have := (hmem (p + 15) (by simp [hSdef])).2; omega
    have hid := identity_head _ hn0
    rw [hid, hU] at hh; injection hh with hh; omega
  have hSne : S ≠ identity S.length := ne_head S (p+3) (by simp [hSdef]) (by omega)
  have hS1ne : S1 ≠ identity S.length := ne_head S1 (p+14) (by simp [hS1def]) (by omega)
  have hS2ne : S2 ≠ identity S.length := ne_head S2 (p+4) (by simp [hS2def]) (by omega)
  have hS3ne : S3 ≠ identity S.length := ne_head S3 (p+7) (by simp [hS3def]) (by omega)
  have hS4ne : S4 ≠ identity S.length := ne_head S4 (p+9) (by simp [hS4def]) (by omega)
  have hS5ne : S5 ≠ identity S.length := ne_head S5 (p+11) (by simp [hS5def]) (by omega)
  have hS6ne : S6 ≠ identity S.length := ne_head S6 (p+6) (by simp [hS6def]) (by omega)
  -- Forced unique steps after the opening flip
  have step2 : ∀ C, EfficientFlip S1 C → C = S2 := by
    intro C hC
    rcases eff_char S1 C hC with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 14 := by
        have := congrArg List.head? (hS1def.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · subst h2
        have hSd' : S1 = [p+14] ++ (p + 15) ::
            ([p+5, p+4, p+13, p+12, p+6, p+9, p+10, p+11, p+8, p+7, p+3, p+2, p+1] ++ Y) := by
          simp [hS1def]
        obtain ⟨e1, -⟩ := split_uniq (p + 15) [p+14] _ ((p + 14) :: A1) B'
          (hSd' ▸ hnd1) (hSd'.symm.trans hSe)
        rw [e1] at hL; simp at hL; subst hL; rw [pq_true_iff] at h1; omega
      · have hb : b = p + 13 := by omega
        subst hb
        obtain ⟨e1, e2⟩ := split_uniq (p + 13) [p+14, p+15, p+5, p+4]
          ([p+12, p+6, p+9, p+10, p+11, p+8, p+7, p+3, p+2, p+1] ++ Y)
          ((p + 14) :: A1) B' (hS1d ▸ hnd1) (hS1d.symm.trans hSe)
        rw [hBe, e1, e2]; simp [hS2def]
    · exfalso; rw [hS1def] at hh1; simp [ha1] at hh1
      have := (memS S1 hS1stack (p + 15) (by simp [hS1def])).2; omega
  have step3 : ∀ D, EfficientFlip S2 D → D = S3 := by
    intro D hD
    rcases eff_char S2 D hD with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 4 := by
        have := congrArg List.head? (hS2def.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · subst h2
        have hSd' : S2 = [p+4] ++ (p + 5) ::
            ([p+15, p+14, p+13, p+12, p+6, p+9, p+10, p+11, p+8, p+7, p+3, p+2, p+1] ++ Y) := by
          simp [hS2def]
        obtain ⟨e1, -⟩ := split_uniq (p + 5) [p+4] _ ((p + 4) :: A1) B'
          (hSd' ▸ hnd2) (hSd'.symm.trans hSe)
        rw [e1] at hL; simp at hL; subst hL; rw [pq_true_iff] at h1; omega
      · have hb : b = p + 3 := by omega
        subst hb
        obtain ⟨e1, e2⟩ := split_uniq (p + 3)
          [p+4, p+5, p+15, p+14, p+13, p+12, p+6, p+9, p+10, p+11, p+8, p+7]
          ([p+2, p+1] ++ Y) ((p + 4) :: A1) B' (hS2d ▸ hnd2) (hS2d.symm.trans hSe)
        rw [hBe, e1, e2]; simp [hS3def]
    · exfalso; rw [hS2def] at hh1; simp [ha1] at hh1
      have := (memS S2 hS2stack (p + 15) (by simp [hS2def])).2; omega
  have step4 : ∀ E, EfficientFlip S3 E → E = S4 := by
    intro E hE
    rcases eff_char S3 E hE with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 7 := by
        have := congrArg List.head? (hS3def.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · subst h2
        have hSd' : S3 = [p+7] ++ (p + 8) ::
            ([p+11, p+10, p+9, p+6, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by
          simp [hS3def]
        obtain ⟨e1, -⟩ := split_uniq (p + 8) [p+7] _ ((p + 7) :: A1) B'
          (hSd' ▸ hnd3) (hSd'.symm.trans hSe)
        rw [e1] at hL; simp at hL; subst hL; rw [pq_true_iff] at h1; omega
      · have hb : b = p + 6 := by omega
        subst hb
        obtain ⟨e1, e2⟩ := split_uniq (p + 6) [p+7, p+8, p+11, p+10, p+9]
          ([p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y)
          ((p + 7) :: A1) B' (hS3d ▸ hnd3) (hS3d.symm.trans hSe)
        rw [hBe, e1, e2]; simp [hS4def]
    · exfalso; rw [hS3def] at hh1; simp [ha1] at hh1
      have := (memS S3 hS3stack (p + 15) (by simp [hS3def])).2; omega
  have step5 : ∀ F, EfficientFlip S4 F → F = S5 := by
    intro F hF
    rcases eff_char S4 F hF with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 9 := by
        have := congrArg List.head? (hS4def.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · subst h2
        have hSd' : S4 = [p+9] ++ (p + 10) ::
            ([p+11, p+8, p+7, p+6, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by
          simp [hS4def]
        obtain ⟨e1, -⟩ := split_uniq (p + 10) [p+9] _ ((p + 9) :: A1) B'
          (hSd' ▸ hnd4) (hSd'.symm.trans hSe)
        rw [e1] at hL; simp at hL; subst hL; rw [pq_true_iff] at h1; omega
      · have hb : b = p + 8 := by omega
        subst hb
        obtain ⟨e1, e2⟩ := split_uniq (p + 8) [p+9, p+10, p+11]
          ([p+7, p+6, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y)
          ((p + 9) :: A1) B' (hS4d ▸ hnd4) (hS4d.symm.trans hSe)
        rw [hBe, e1, e2]; simp [hS5def]
    · exfalso; rw [hS4def] at hh1; simp [ha1] at hh1
      have := (memS S4 hS4stack (p + 15) (by simp [hS4def])).2; omega
  have step6 : ∀ G, EfficientFlip S5 G → G = S6 := by
    intro G hG
    rcases eff_char S5 G hG with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 11 := by
        have := congrArg List.head? (hS5def.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · subst h2
        -- b = p+12 good
        obtain ⟨e1, e2⟩ := split_uniq (p + 12) [p+11, p+10, p+9, p+8, p+7, p+6]
          ([p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y)
          ((p + 11) :: A1) B' (hS5d ▸ hnd5) (hS5d.symm.trans hSe)
        rw [hBe, e1, e2]; simp [hS6def]
      · have hb : b = p + 10 := by omega
        subst hb
        have hSd' : S5 = [p+11] ++ (p + 10) ::
            ([p+9, p+8, p+7, p+6, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by
          simp [hS5def]
        obtain ⟨e1, -⟩ := split_uniq (p + 10) [p+11] _ ((p + 11) :: A1) B'
          (hSd' ▸ hnd5) (hSd'.symm.trans hSe)
        rw [e1] at hL; simp at hL; subst hL; rw [pq_true_iff] at h1; omega
    · exfalso; rw [hS5def] at hh1; simp [ha1] at hh1
      have := (memS S5 hS5stack (p + 15) (by simp [hS5def])).2; omega
  have step7 : ∀ H, EfficientFlip S6 H → H = T := by
    intro H hH
    rcases eff_char S6 H hH with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 6 := by
        have := congrArg List.head? (hS6def.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · subst h2
        have hSd' : S6 = [p+6] ++ (p + 7) ::
            ([p+8, p+9, p+10, p+11, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y) := by
          simp [hS6def]
        obtain ⟨e1, -⟩ := split_uniq (p + 7) [p+6] _ ((p + 6) :: A1) B'
          (hSd' ▸ hnd6) (hSd'.symm.trans hSe)
        rw [e1] at hL; simp at hL; subst hL; rw [pq_true_iff] at h1; omega
      · have hb : b = p + 5 := by omega
        subst hb
        obtain ⟨e1, e2⟩ := split_uniq (p + 5)
          [p+6, p+7, p+8, p+9, p+10, p+11, p+12, p+13, p+14, p+15]
          ([p+4, p+3, p+2, p+1] ++ Y) ((p + 6) :: A1) B'
          (hS6d ▸ hnd6) (hS6d.symm.trans hSe)
        rw [hBe, e1, e2, hTeq]
    · exfalso; rw [hS6def] at hh1; simp [ha1] at hh1
      have := (memS S6 hS6stack (p + 15) (by simp [hS6def])).2; omega
  refine ⟨?exist, ?unique⟩
  · intro T' hT'; rw [Set.mem_singleton_iff] at hT'; subst hT'
    refine ⟨[S, S1, S2, S3, S4, S5, S6, T], rfl, ?_, ?_⟩
    · simpa [hT_int] using (rfl : [S, S1, S2, S3, S4, S5, S6, T].getLast? = some T)
    · refine List.isChain_cons_cons.mpr ⟨eff1, ?_⟩
      refine List.isChain_cons_cons.mpr ⟨eff2, ?_⟩
      refine List.isChain_cons_cons.mpr ⟨eff3, ?_⟩
      refine List.isChain_cons_cons.mpr ⟨eff4, ?_⟩
      refine List.isChain_cons_cons.mpr ⟨eff5, ?_⟩
      refine List.isChain_cons_cons.mpr ⟨eff6, ?_⟩
      exact List.isChain_cons_cons.mpr ⟨eff7, List.isChain_singleton _⟩
  · intro π hπ
    obtain ⟨hh, hl, hc⟩ := hπ
    rcases π with _ | ⟨A, rest⟩
    · simp at hh
    · simp only [List.head?_cons, Option.some.injEq] at hh; subst hh
      rcases rest with _ | ⟨B, rest2⟩
      · simp at hl; exact absurd hl hSne
      · rw [List.isChain_cons_cons] at hc
        rcases eff_char S B hc.1 with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
        · have ha1 : a1 = p + 3 := by
            have := congrArg List.head? (hSdef.symm.trans hSe); simpa [eq_comm] using this
          subst ha1; rw [pq_false_iff] at h2
          rcases h2 with h2 | h2
          · -- alt flip 9 -> deadlock
            subst h2
            have hSdAlt : S = [p+3, p+7, p+8, p+11, p+10, p+9, p+6, p+12, p+13] ++
                (p + 4) :: ([p+5, p+15, p+14, p+2, p+1] ++ Y) := by rw [hSdef]; simp
            obtain ⟨e1, e2⟩ := split_uniq (p + 4)
              [p+3, p+7, p+8, p+11, p+10, p+9, p+6, p+12, p+13]
              ([p+5, p+15, p+14, p+2, p+1] ++ Y) ((p + 3) :: A1) B'
              (hSdAlt ▸ hnd) (hSdAlt.symm.trans hSe)
            set Bdl := [p+13, p+12, p+6, p+9, p+10, p+11, p+8, p+7, p+3, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y
            have hBeq : B = Bdl := by rw [hBe, e1, e2]; simp [Bdl]
            subst hBeq
            have hDL := deadlock_alt_f2 p Y (by simpa [forkF2_eq] using (show IsStack (forkF2 p ++ Y) from hS))
            have hBne : Bdl ≠ identity S.length := ne_head Bdl (p+13) (by simp [Bdl]) (by omega)
            rcases rest2 with _ | ⟨C, _⟩
            · simp at hl; exact absurd hl hBne
            · exact absurd (List.isChain_cons_cons.mp hc.2).1 (hDL.2 C)
          · -- good flip 13
            have hb : b = p + 2 := by omega
            subst hb
            obtain ⟨e1, e2⟩ := split_uniq (p + 2)
              [p+3, p+7, p+8, p+11, p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14]
              ([p+1] ++ Y) ((p + 3) :: A1) B' (hSd ▸ hnd) (hSd.symm.trans hSe)
            have hBeq : B = S1 := by
              rw [hBe, e1, e2]
              simp [hS1def]
            subst hBeq
            rcases rest2 with _ | ⟨C, rest3⟩
            · simp at hl; exact absurd hl hS1ne
            · have hC : C = S2 := step2 C (List.isChain_cons_cons.mp hc.2).1
              subst hC
              rcases rest3 with _ | ⟨D, rest4⟩
              · simp at hl; exact absurd hl hS2ne
              · have hc2 := (List.isChain_cons_cons.mp hc.2).2
                have hD : D = S3 := step3 D (List.isChain_cons_cons.mp hc2).1
                subst hD
                rcases rest4 with _ | ⟨E, rest5⟩
                · simp at hl; exact absurd hl hS3ne
                · have hc3 := (List.isChain_cons_cons.mp hc2).2
                  have hE : E = S4 := step4 E (List.isChain_cons_cons.mp hc3).1
                  subst hE
                  rcases rest5 with _ | ⟨F, rest6⟩
                  · simp at hl; exact absurd hl hS4ne
                  · have hc4 := (List.isChain_cons_cons.mp hc3).2
                    have hF : F = S5 := step5 F (List.isChain_cons_cons.mp hc4).1
                    subst hF
                    rcases rest6 with _ | ⟨G, rest7⟩
                    · simp at hl; exact absurd hl hS5ne
                    · have hc5 := (List.isChain_cons_cons.mp hc4).2
                      have hG : G = S6 := step6 G (List.isChain_cons_cons.mp hc5).1
                      subst hG
                      rcases rest7 with _ | ⟨H, rest8⟩
                      · simp at hl; exact absurd hl hS6ne
                      · have hc6 := (List.isChain_cons_cons.mp hc5).2
                        have hH : H = T := step7 H (List.isChain_cons_cons.mp hc6).1
                        subst hH
                        exact ⟨(interval (p + 1) (p + 15)).reverse ++ Y, by simp [hT_int], by simp [hT_int]⟩
        · exfalso
          rw [hSdef] at hh1; simp [ha1] at hh1
          have := (hmem (p + 15) (by simp [hSdef])).2; omega

/-! ### Part (a): fork opening -/

private lemma x_ne_forkF (p : ℕ) (X Y : List ℕ) (x z : ℕ)
    (hnd : ([p+11, p+8, p+7, p+3] ++ X ++
      [p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y).Nodup)
    (hx : x ∈ X)
    (hz : z ∈ ([p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] : List ℕ))
    (hxz : x = z) : False := by
  subst hxz
  refine false_of_nodup_parts (A := [p+11, p+8, p+7, p+3] ++ X)
    (B := [p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y)
    (by simpa [List.append_assoc] using hnd)
    (List.mem_append_right _ hx) (List.mem_append_left _ hz)

private lemma x_ne_forkE (p : ℕ) (X Y : List ℕ) (x z : ℕ)
    (hnd : ([p+11, p+8, p+7, p+3] ++ X ++
      [p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y).Nodup)
    (hx : x ∈ X)
    (hz : z ∈ ([p+11, p+8, p+7, p+3] : List ℕ))
    (hxz : x = z) : False := by
  subst hxz
  refine false_of_nodup_parts (A := [p+11, p+8, p+7, p+3]) (B := X ++
      ([p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y))
    (by
      have : [p+11, p+8, p+7, p+3] ++ X ++
          [p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y =
        [p+11, p+8, p+7, p+3] ++ (X ++
          ([p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y)) := by
        simp [List.append_assoc]
      simpa [this] using hnd)
    hz (List.mem_append_left _ hx)

private theorem eff_to_T2 (p : ℕ) (X Y : List ℕ)
    (hS : IsStack (forkE p ++ X ++ forkF p ++ Y)) :
    EfficientFlip (forkE p ++ X ++ forkF p ++ Y)
      (X.reverse ++ forkF2 p ++ Y) := by
  set S := forkE p ++ X ++ forkF p ++ Y with hSdef
  have hnd := stack_nodup S hS
  rw [forkE_eq, forkF_eq] at hSdef
  set T2 := X.reverse ++ forkF2 p ++ Y
  have hSd : S = ([p+11, p+8, p+7, p+3] ++ X) ++ (p + 10) ::
      ([p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
    rw [hSdef]; simp
  cases hX : X with
  | nil =>
    have hL : ([p+11, p+8, p+7, p+3] ++ X).getLast? = some (p + 3) := by rw [hX]; simp
    have h := eff_of (p + 11) ([p+8, p+7, p+3] ++ X) (p + 3)
      (by simpa [List.cons_append, hX] using hL) (p + 10)
      ([p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    have hT2eq : T2 = ([p+11, p+8, p+7, p+3] ++ X).reverse ++ (p + 10) ::
        ([p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
      simp [T2, hX, forkF2_eq]
    simpa [hSdef, hSd, hT2eq, hX, T2] using h
  | cons x X' =>
    have hnd0 : ([p+11, p+8, p+7, p+3] ++ X ++
        [p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y).Nodup := by
      simpa [hSdef] using hnd
    have hL0 : ([p+11, p+8, p+7, p+3] ++ X).getLast? = (x :: X').getLast? := by
      rw [hX]; simp [List.getLast?_append]
    obtain ⟨aL, hAL⟩ : ∃ aL, (x :: X').getLast? = some aL :=
      ⟨(x :: X').getLast (by simp), List.getLast?_eq_some_getLast _⟩
    have haL_mem : aL ∈ X := by
      obtain ⟨as, has⟩ := List.getLast?_eq_some_iff.mp hAL
      have : aL ∈ x :: X' := has ▸ List.mem_append_right _ (List.mem_singleton_self aL)
      simpa [hX] using this
    have hne9 : aL ≠ p + 9 := fun h => x_ne_forkF p X Y aL (p+9) hnd0 haL_mem (by simp) h
    have hne10 : aL ≠ p + 10 := fun h => x_ne_forkF p X Y aL (p+10) hnd0 haL_mem (by simp) h
    have hne11 : aL ≠ p + 11 := fun h => x_ne_forkE p X Y aL (p+11) hnd0 haL_mem (by simp) h
    have hL : ([p+11, p+8, p+7, p+3] ++ X).getLast? = some aL := by rw [hL0, hAL]
    have hL' : ((p + 11) :: ([p+8, p+7, p+3] ++ X)).getLast? = some aL := by
      simpa [List.cons_append] using hL
    have h := eff_of (p + 11) ([p+8, p+7, p+3] ++ X) aL hL' (p + 10)
      ([p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y)
      (by
        rw [pq_true_iff]; intro h
        rcases h with h | h
        · exact hne10 (by omega)
        · exact hne9 (by omega))
      (by rw [pq_false_iff]; exact Or.inr (by omega))
    have hT2eq : T2 = ([p+11, p+8, p+7, p+3] ++ X).reverse ++ (p + 10) ::
        ([p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
      simp [T2, forkF2_eq, List.reverse_append]
    simpa [hSdef, hSd, hT2eq, T2] using h

/-! ### Part (a): fork opening to {X++F¹++Y, ★X++F²++Y} -/

/-- Bad second cut on the T1 path (flip `9+|X|` instead of `13+|X|`) is a deadlock. -/
private theorem deadlock_alt_fork_a (p : ℕ) (X Y : List ℕ)
    (hS : IsStack (forkE p ++ X ++ forkF p ++ Y)) :
    IsDeadlock ([p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++
      [p+3, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
  set B := [p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++
      [p+3, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y with hBdef
  set S0 := forkE p ++ X ++ forkF p ++ Y
  -- B is a double reverse of prefixes of S0 along the T1 path; establish Perm via the known path
  have hS0eq : S0 = [p+11, p+8, p+7, p+3] ++ X ++
      [p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y := by
    simp [S0, forkE_eq, forkF_eq, List.append_assoc]
  set S1 := [p+6, p+9, p+10] ++ X.reverse ++
      [p+3, p+7, p+8, p+11, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y
  set S2 := [p+3] ++ X ++
      [p+10, p+9, p+6, p+7, p+8, p+11, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y
  have hS1eq : S1 =
      ([p+11, p+8, p+7, p+3] ++ X ++ [p+10, p+9, p+6]).reverse ++
        ([p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
    simp [S1, List.reverse_append, List.reverse_cons, List.append_assoc]
  have hS2eq : S2 =
      ([p+6, p+9, p+10] ++ X.reverse ++ [p+3]).reverse ++
        ([p+7, p+8, p+11, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
    simp [S2, List.reverse_append, List.reverse_cons, List.append_assoc]
  have hBeq : B =
      ([p+3] ++ X ++ [p+10, p+9, p+6, p+7, p+8, p+11, p+12, p+13]).reverse ++
        ([p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
    simp [hBdef, List.reverse_append, List.reverse_cons, List.append_assoc]
  have hperm1 : S1.Perm S0 := by
    rw [hS1eq, hS0eq]
    have : [p+11, p+8, p+7, p+3] ++ X ++
        [p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y =
      ([p+11, p+8, p+7, p+3] ++ X ++ [p+10, p+9, p+6]) ++
        ([p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
      simp [List.append_assoc]
    rw [this]; exact (List.reverse_perm _).append_right _
  have hperm2 : S2.Perm S1 := by
    have hS1d : S1 = ([p+6, p+9, p+10] ++ X.reverse ++ [p+3]) ++
        ([p+7, p+8, p+11, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
      simp [S1, List.append_assoc]
    rw [hS1d, hS2eq]; exact (List.reverse_perm _).append_right _
  have hperm3 : B.Perm S2 := by
    have hS2d : S2 = ([p+3] ++ X ++ [p+10, p+9, p+6, p+7, p+8, p+11, p+12, p+13]) ++
        ([p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
      simp [S2, List.append_assoc]
    rw [hS2d, hBeq]; exact (List.reverse_perm _).append_right _
  have hperm : B.Perm S0 := hperm3.trans (hperm2.trans hperm1)
  have hBstack : IsStack B := by
    unfold IsStack; rw [hperm.length_eq]; exact hperm.trans hS
  have hnd := stack_nodup B hBstack
  have hmem := memS B hBstack
  have hne : B ≠ identity B.length := by
    intro h
    have hh := congrArg List.head? h
    have hn0 : 1 ≤ B.length := by
      have := (hmem (p + 13) (by simp [hBdef])).2; omega
    have hid := identity_head _ hn0
    have hhd : B.head? = some (p + 13) := by simp [hBdef]
    rw [hid, hhd] at hh; injection hh with hh; omega
  refine ⟨hne, ?_⟩
  intro S' hEff
  rcases eff_flip_form hEff (by
    intro a ha haLen
    have : a = p + 13 := by
      have hhd : B.head? = some (p + 13) := by simp [hBdef]
      have := hhd.symm.trans ha; injection this with this; exact this.symm
    have := (hmem (p + 15) (by simp [hBdef])).2; omega) with
    ⟨a1, A1, aL, b, Brest, hL, hSe, hBe, h1, h2⟩
  have ha1 : a1 = p + 13 := by
    have := congrArg List.head? (hBdef.symm.trans hSe); simpa [eq_comm] using this
  subst ha1; rw [pq_false_iff] at h2
  rcases h2 with h2 | h2
  · -- b = p+14
    subst h2
    have hBd : B = ([p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++
        [p+3, p+4, p+5, p+15]) ++ (p + 14) :: ([p+2, p+1] ++ Y) := by
      rw [hBdef]; simp [List.append_assoc]
    obtain ⟨e1, -⟩ := split_uniq (p + 14)
      ([p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++
        [p+3, p+4, p+5, p+15])
      ([p+2, p+1] ++ Y) ((p + 13) :: A1) Brest (hBd ▸ hnd) (hBd.symm.trans hSe)
    have hL' : ([p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++
        [p+3, p+4, p+5, p+15]).getLast? = some (p + 15) := by
      rw [show [p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++
            [p+3, p+4, p+5, p+15] =
          ([p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++
            [p+3, p+4, p+5]) ++ [p + 15] by simp]
      exact getLast_snoc _ _
    rw [e1, hL'] at hL; injection hL with hL; subst hL
    rw [pq_true_iff] at h1; omega
  · -- b = p+12
    have hb : b = p + 12 := by omega
    subst hb
    have hBd : B = [p+13] ++ (p + 12) ::
        ([p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++
          [p+3, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
      rw [hBdef]; simp [List.append_assoc]
    obtain ⟨e1, -⟩ := split_uniq (p + 12) [p+13] _ ((p + 13) :: A1) Brest
      (hBd ▸ hnd) (hBd.symm.trans hSe)
    rw [e1] at hL; simp at hL; subst hL
    rw [pq_true_iff] at h1; omega


theorem prop7_a (p : ℕ) (X Y : List ℕ)
    (hS : IsStack (forkE p ++ X ++ forkF p ++ Y)) :
    LeadsTo (forkE p ++ X ++ forkF p ++ Y)
      {X ++ forkF1 p ++ Y, X.reverse ++ forkF2 p ++ Y} := by
  set S := forkE p ++ X ++ forkF p ++ Y with hSdef
  have hnd := stack_nodup S hS
  have hmem := memS S hS
  rw [forkE_eq, forkF_eq] at hSdef
  set T2 := X.reverse ++ forkF2 p ++ Y
  set T1 := X ++ forkF1 p ++ Y
  set S1 := [p+6, p+9, p+10] ++ X.reverse ++
      [p+3, p+7, p+8, p+11, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y with hS1def
  set S2 := [p+3] ++ X ++
      [p+10, p+9, p+6, p+7, p+8, p+11, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y with hS2def
  set S3 := [p+14, p+15, p+5, p+4, p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++
      [p+3, p+2, p+1] ++ Y with hS3def
  set S4 := [p+4, p+5, p+15, p+14, p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++
      [p+3, p+2, p+1] ++ Y with hS4def
  have hT1eq : T1 = X ++
      [p+10, p+9, p+6, p+7, p+8, p+11, p+12, p+13, p+14, p+15, p+5, p+4, p+3, p+2, p+1] ++ Y := by
    simp [T1, forkF1_eq]
  have hT2eq' : T2 = X.reverse ++
      [p+3, p+7, p+8, p+11, p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y := by
    simp [T2, forkF2_eq]
  -- first flip to S1: reverse E++X++[10,9,6], join p+12
  have hSd : S = ([p+11, p+8, p+7, p+3] ++ X ++ [p+10, p+9, p+6]) ++
      (p + 12) :: ([p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
    rw [hSdef]; simp [List.append_assoc]
  have hS1rev : S1 =
      ([p+11, p+8, p+7, p+3] ++ X ++ [p+10, p+9, p+6]).reverse ++
        (p + 12) :: ([p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
    simp [hS1def, List.reverse_append, List.reverse_cons, List.append_assoc]
  have hpref1 :
      ([p+11, p+8, p+7, p+3] ++ X ++ [p+10, p+9, p+6]).getLast? = some (p + 6) := by
    rw [show [p+11, p+8, p+7, p+3] ++ X ++ [p+10, p+9, p+6] =
          ([p+11, p+8, p+7, p+3] ++ X ++ [p+10, p+9]) ++ [p + 6] by simp]
    exact getLast_snoc _ _
  have eff1 : EfficientFlip S S1 := by
    have h := eff_of (p + 11) ([p+8, p+7, p+3] ++ X ++ [p+10, p+9, p+6]) (p + 6)
      (by simpa [List.cons_append, List.append_assoc] using hpref1)
      (p + 12) ([p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    simpa [hSd, hS1rev, List.cons_append] using h
  -- second flip S1 → S2
  have hS1d : S1 = ([p+6, p+9, p+10] ++ X.reverse ++ [p+3]) ++
      (p + 7) :: ([p+8, p+11, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
    simp [hS1def, List.append_assoc]
  have hS2rev : S2 =
      ([p+6, p+9, p+10] ++ X.reverse ++ [p+3]).reverse ++
        (p + 7) :: ([p+8, p+11, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
    simp [hS2def, List.reverse_append, List.reverse_cons, List.append_assoc]
  have eff2 : EfficientFlip S1 S2 := by
    have hL : ([p+6, p+9, p+10] ++ X.reverse ++ [p+3]).getLast? = some (p + 3) := by
      rw [show [p+6, p+9, p+10] ++ X.reverse ++ [p+3] =
            ([p+6, p+9, p+10] ++ X.reverse) ++ [p + 3] by simp]
      exact getLast_snoc _ _
    have h := eff_of (p + 6) ([p+9, p+10] ++ X.reverse ++ [p+3]) (p + 3)
      (by simpa [List.cons_append] using hL)
      (p + 7) ([p+8, p+11, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    simpa [hS1d, hS2rev, List.cons_append] using h
  -- third flip S2 → S3 (through p+14)
  have hS2d : S2 = ([p+3] ++ X ++ [p+10, p+9, p+6, p+7, p+8, p+11, p+12, p+13, p+4, p+5, p+15, p+14]) ++
      (p + 2) :: ([p+1] ++ Y) := by
    simp [hS2def, List.append_assoc]
  have hS3rev : S3 =
      ([p+3] ++ X ++ [p+10, p+9, p+6, p+7, p+8, p+11, p+12, p+13, p+4, p+5, p+15, p+14]).reverse ++
        (p + 2) :: ([p+1] ++ Y) := by
    simp [hS3def, List.reverse_append, List.reverse_cons, List.append_assoc]
  have hpref3 :
      ([p+3] ++ X ++ [p+10, p+9, p+6, p+7, p+8, p+11, p+12, p+13, p+4, p+5, p+15, p+14]).getLast? =
        some (p + 14) := by
    rw [show [p+3] ++ X ++ [p+10, p+9, p+6, p+7, p+8, p+11, p+12, p+13, p+4, p+5, p+15, p+14] =
          ([p+3] ++ X ++ [p+10, p+9, p+6, p+7, p+8, p+11, p+12, p+13, p+4, p+5, p+15]) ++ [p + 14] by simp]
    exact getLast_snoc _ _
  have eff3 : EfficientFlip S2 S3 := by
    have h := eff_of (p + 3) (X ++ [p+10, p+9, p+6, p+7, p+8, p+11, p+12, p+13, p+4, p+5, p+15, p+14])
      (p + 14) (by simpa [List.cons_append, List.append_assoc] using hpref3)
      (p + 2) ([p+1] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    simpa [hS2d, hS3rev, List.cons_append] using h
  -- fourth flip S3 → S4
  have hS3d : S3 = [p+14, p+15, p+5, p+4] ++
      (p + 13) :: ([p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++ [p+3, p+2, p+1] ++ Y) := by
    simp [hS3def, List.append_assoc]
  have hS4rev : S4 = [p+14, p+15, p+5, p+4].reverse ++
      (p + 13) :: ([p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++ [p+3, p+2, p+1] ++ Y) := by
    simp [hS4def, List.append_assoc]
  have eff4 : EfficientFlip S3 S4 := by
    have h := eff_of (p + 14) [p+15, p+5, p+4] (p + 4) (by simp) (p + 13)
      ([p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++ [p+3, p+2, p+1] ++ Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    simpa [hS3d, hS4rev] using h
  -- fifth flip S4 → T1
  have hS4d : S4 = ([p+4, p+5, p+15, p+14, p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse) ++
      (p + 3) :: ([p+2, p+1] ++ Y) := by
    simp [hS4def, List.append_assoc]
  have hT1rev : T1 =
      ([p+4, p+5, p+15, p+14, p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse).reverse ++
        (p + 3) :: ([p+2, p+1] ++ Y) := by
    simp [hT1eq, List.reverse_append, List.reverse_cons, List.append_assoc]
  have eff5 : EfficientFlip S4 T1 := by
    cases hX : X with
    | nil =>
      have hL : ([p+4, p+5, p+15, p+14, p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++
          X.reverse).getLast? = some (p + 10) := by
        rw [hX]
        change ([p+4, p+5, p+15, p+14, p+13, p+12, p+11, p+8, p+7, p+6, p+9] ++ [p+10]).getLast? =
          some (p + 10)
        exact getLast_snoc _ _
      have h := eff_of (p + 4)
        ([p+5, p+15, p+14, p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse) (p + 10)
        (by simpa [List.cons_append, hX] using hL)
        (p + 3) ([p+2, p+1] ++ Y)
        (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
      simpa [hS4d, hT1rev, List.cons_append, hX] using h
    | cons x X' =>
      have hnd0 : ([p+11, p+8, p+7, p+3] ++ X ++
          [p+10, p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y).Nodup := by
        simpa [hSdef] using hnd
      have hx : x ∈ X := by simp [hX]
      have hx_ne3 : x ≠ p + 3 := fun h => x_ne_forkE p X Y x (p+3) hnd0 hx (by simp) h
      have hx_ne4 : x ≠ p + 4 := fun h => x_ne_forkF p X Y x (p+4) hnd0 hx (by simp) h
      have hx_ne2 : x ≠ p + 2 := fun h => x_ne_forkF p X Y x (p+2) hnd0 hx (by simp) h
      have hx_ne10 : x ≠ p + 10 := fun h => x_ne_forkF p X Y x (p+10) hnd0 hx (by simp) h
      have hL : ([p+4, p+5, p+15, p+14, p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++
          X.reverse).getLast? = some x := by
        rw [hX, List.reverse_cons, ← List.append_assoc]
        exact getLast_snoc _ _
      have h := eff_of (p + 4)
        ([p+5, p+15, p+14, p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse) x
        (by simpa [List.cons_append] using hL)
        (p + 3) ([p+2, p+1] ++ Y)
        (by rw [pq_true_iff]; clear hL; omega) (by rw [pq_false_iff]; omega)
      simpa [hS4d, hT1rev, List.cons_append] using h
  -- stack facts along the path
  have hperm1 : S1.Perm S := by
    rw [hS1rev, hSd]; exact (List.reverse_perm _).append_right _
  have hS1stack : IsStack S1 := by
    unfold IsStack; rw [hperm1.length_eq]; exact hperm1.trans hS
  have hnd1 := stack_nodup S1 hS1stack
  have hperm2 : S2.Perm S1 := by
    rw [show S1 = ([p+6, p+9, p+10] ++ X.reverse ++ [p+3]) ++
        (p + 7) :: ([p+8, p+11, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) from hS1d,
      hS2rev]
    exact (List.reverse_perm _).append_right _
  have hS2stack : IsStack S2 := by
    unfold IsStack; rw [hperm2.length_eq, hperm1.length_eq]
    exact hperm2.trans (hperm1.trans hS)
  have hnd2 := stack_nodup S2 hS2stack
  have hperm3 : S3.Perm S2 := by
    rw [hS2d, hS3rev]; exact (List.reverse_perm _).append_right _
  have hS3stack : IsStack S3 := by
    unfold IsStack; rw [hperm3.length_eq, hperm2.length_eq, hperm1.length_eq]
    exact hperm3.trans (hperm2.trans (hperm1.trans hS))
  have hnd3 := stack_nodup S3 hS3stack
  have hperm4 : S4.Perm S3 := by
    rw [hS3d, hS4rev]; exact (List.reverse_perm _).append_right _
  have hS4stack : IsStack S4 := by
    unfold IsStack; rw [hperm4.length_eq, hperm3.length_eq, hperm2.length_eq, hperm1.length_eq]
    exact hperm4.trans (hperm3.trans (hperm2.trans (hperm1.trans hS)))
  have hnd4 := stack_nodup S4 hS4stack
  have ne_head (U : List ℕ) (u : ℕ) (hU : U.head? = some u) (hu : 1 < u ∨ u = 0) :
      U ≠ identity U.length := by
    intro h; have hh := congrArg List.head? h
    have hn0 : 1 ≤ U.length := by
      cases hU' : U.head? with
      | none => simp [hU'] at hU
      | some _ =>
        have : U ≠ [] := by intro he; simp [he] at hU'
        exact Nat.succ_le_of_lt (List.length_pos_of_ne_nil this)
    have hid := identity_head _ hn0
    rw [hid, hU] at hh; injection hh with hh; omega
  have hSne : S ≠ identity S.length := ne_head S (p+11) (by simp [hSdef]) (by omega)
  have hS1ne : S1 ≠ identity S.length := by
    have := ne_head S1 (p+6) (by simp [hS1def]) (by omega)
    rwa [hperm1.length_eq] at this
  have hS2ne : S2 ≠ identity S.length := by
    have := ne_head S2 (p+3) (by simp [hS2def]) (by omega)
    rwa [hperm2.length_eq, hperm1.length_eq] at this
  have hS3ne : S3 ≠ identity S.length := by
    have := ne_head S3 (p+14) (by simp [hS3def]) (by omega)
    rwa [hperm3.length_eq, hperm2.length_eq, hperm1.length_eq] at this
  have hS4ne : S4 ≠ identity S.length := by
    have := ne_head S4 (p+4) (by simp [hS4def]) (by omega)
    rwa [hperm4.length_eq, hperm3.length_eq, hperm2.length_eq, hperm1.length_eq] at this
  -- T2 one-step path
  have effT2 : EfficientFlip S T2 := by
    simpa [S, T2, hSdef.symm, forkE_eq, forkF_eq] using eff_to_T2 p X Y hS
  -- uniqueness of each T1 step
  have step1 : ∀ B, EfficientFlip S B → B = S1 ∨ B = T2 := by
    intro B hB
    rcases eff_char S B hB with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 11 := by
        have := congrArg List.head? (hSdef.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · -- b = p+12 → S1
        subst h2
        obtain ⟨e1, e2⟩ := split_uniq (p + 12)
          ([p+11, p+8, p+7, p+3] ++ X ++ [p+10, p+9, p+6])
          ([p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y)
          ((p + 11) :: A1) B' (hSd ▸ hnd) (hSd.symm.trans hSe)
        left; rw [hBe, e1, e2, ← hS1rev]
      · -- b = p+10 → T2
        have hb : b = p + 10 := by omega
        subst hb
        have hSdT : S = ([p+11, p+8, p+7, p+3] ++ X) ++
            (p + 10) :: ([p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
          rw [hSdef]; simp [List.append_assoc]
        obtain ⟨e1, e2⟩ := split_uniq (p + 10)
          ([p+11, p+8, p+7, p+3] ++ X)
          ([p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y)
          ((p + 11) :: A1) B' (hSdT ▸ hnd) (hSdT.symm.trans hSe)
        right
        have hT2rev : T2 = ([p+11, p+8, p+7, p+3] ++ X).reverse ++
            (p + 10) :: ([p+9, p+6, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y) := by
          simp [hT2eq', List.reverse_append, List.reverse_cons, List.append_assoc]
        rw [hBe, e1, e2, ← hT2rev]
    · exfalso
      rw [hSdef] at hh1; simp [ha1] at hh1
      have := (hmem (p + 15) (by simp [hSdef])).2; omega
  have step2 : ∀ C, EfficientFlip S1 C → C = S2 := by
    intro C hC
    rcases eff_char S1 C hC with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 6 := by
        have := congrArg List.head? (hS1def.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · -- b = p+7 good
        subst h2
        obtain ⟨e1, e2⟩ := split_uniq (p + 7)
          ([p+6, p+9, p+10] ++ X.reverse ++ [p+3])
          ([p+8, p+11, p+12, p+13, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y)
          ((p + 6) :: A1) B' (hS1d ▸ hnd1) (hS1d.symm.trans hSe)
        rw [hBe, e1, e2, ← hS2rev]
      · -- b = p+5 bad
        have hb : b = p + 5 := by omega
        subst hb
        have hSdAlt : S1 = ([p+6, p+9, p+10] ++ X.reverse ++
            [p+3, p+7, p+8, p+11, p+12, p+13, p+4]) ++
            (p + 5) :: ([p+15, p+14, p+2, p+1] ++ Y) := by
          simp [hS1def, List.append_assoc]
        obtain ⟨e1, -⟩ := split_uniq (p + 5)
          ([p+6, p+9, p+10] ++ X.reverse ++ [p+3, p+7, p+8, p+11, p+12, p+13, p+4])
          ([p+15, p+14, p+2, p+1] ++ Y) ((p + 6) :: A1) B'
          (hSdAlt ▸ hnd1) (hSdAlt.symm.trans hSe)
        have hL' : ([p+6, p+9, p+10] ++ X.reverse ++
            [p+3, p+7, p+8, p+11, p+12, p+13, p+4]).getLast? = some (p + 4) := by
          rw [show [p+6, p+9, p+10] ++ X.reverse ++
                [p+3, p+7, p+8, p+11, p+12, p+13, p+4] =
              ([p+6, p+9, p+10] ++ X.reverse ++
                [p+3, p+7, p+8, p+11, p+12, p+13]) ++ [p + 4] by simp]
          exact getLast_snoc _ _
        rw [e1, hL'] at hL; injection hL with hL; subst hL
        rw [pq_true_iff] at h1; omega
    · exfalso; rw [hS1def] at hh1; simp [ha1] at hh1
      have := (memS S1 hS1stack (p + 15) (by simp [hS1def])).2; omega
  have step3 : ∀ D, EfficientFlip S2 D → D = S3 ∨
      D = [p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++
        [p+3, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y := by
    intro D hD
    rcases eff_char S2 D hD with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 3 := by
        have := congrArg List.head? (hS2def.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · -- b = p+4 → alt deadlock state
        subst h2
        have hSdAlt : S2 = ([p+3] ++ X ++ [p+10, p+9, p+6, p+7, p+8, p+11, p+12, p+13]) ++
            (p + 4) :: ([p+5, p+15, p+14, p+2, p+1] ++ Y) := by
          simp [hS2def, List.append_assoc]
        obtain ⟨e1, e2⟩ := split_uniq (p + 4)
          ([p+3] ++ X ++ [p+10, p+9, p+6, p+7, p+8, p+11, p+12, p+13])
          ([p+5, p+15, p+14, p+2, p+1] ++ Y)
          ((p + 3) :: A1) B' (hSdAlt ▸ hnd2) (hSdAlt.symm.trans hSe)
        right
        have hAlt : [p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++
            [p+3, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y =
          ([p+3] ++ X ++ [p+10, p+9, p+6, p+7, p+8, p+11, p+12, p+13]).reverse ++
            (p + 4) :: ([p+5, p+15, p+14, p+2, p+1] ++ Y) := by
          simp [List.reverse_append, List.reverse_cons, List.append_assoc]
        rw [hBe, e1, e2, ← hAlt]
      · -- b = p+2 → S3
        have hb : b = p + 2 := by omega
        subst hb
        obtain ⟨e1, e2⟩ := split_uniq (p + 2)
          ([p+3] ++ X ++ [p+10, p+9, p+6, p+7, p+8, p+11, p+12, p+13, p+4, p+5, p+15, p+14])
          ([p+1] ++ Y) ((p + 3) :: A1) B' (hS2d ▸ hnd2) (hS2d.symm.trans hSe)
        left; rw [hBe, e1, e2, ← hS3rev]
    · exfalso; rw [hS2def] at hh1; simp [ha1] at hh1
      have := (memS S2 hS2stack (p + 15) (by simp [hS2def])).2; omega
  have step4 : ∀ E, EfficientFlip S3 E → E = S4 := by
    intro E hE
    rcases eff_char S3 E hE with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 14 := by
        have := congrArg List.head? (hS3def.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · -- b = p+15 bad
        subst h2
        have hSdAlt : S3 = [p+14] ++ (p + 15) ::
            ([p+5, p+4, p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++
              [p+3, p+2, p+1] ++ Y) := by
          simp [hS3def, List.append_assoc]
        obtain ⟨e1, -⟩ := split_uniq (p + 15) [p+14] _ ((p + 14) :: A1) B'
          (hSdAlt ▸ hnd3) (hSdAlt.symm.trans hSe)
        rw [e1] at hL; simp at hL; subst hL
        rw [pq_true_iff] at h1; omega
      · -- b = p+13 good
        have hb : b = p + 13 := by omega
        subst hb
        obtain ⟨e1, e2⟩ := split_uniq (p + 13) [p+14, p+15, p+5, p+4]
          ([p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++ [p+3, p+2, p+1] ++ Y)
          ((p + 14) :: A1) B' (hS3d ▸ hnd3) (hS3d.symm.trans hSe)
        rw [hBe, e1, e2, ← hS4rev]
    · exfalso; rw [hS3def] at hh1; simp [ha1] at hh1
      have := (memS S3 hS3stack (p + 15) (by simp [hS3def])).2; omega
  have step5 : ∀ F, EfficientFlip S4 F → F = T1 := by
    intro F hF
    rcases eff_char S4 F hF with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : a1 = p + 4 := by
        have := congrArg List.head? (hS4def.symm.trans hSe); simpa [eq_comm] using this
      subst ha1; rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · -- b = p+5 bad
        subst h2
        have hSdAlt : S4 = [p+4] ++ (p + 5) ::
            ([p+15, p+14, p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++
              [p+3, p+2, p+1] ++ Y) := by
          simp [hS4def, List.append_assoc]
        obtain ⟨e1, -⟩ := split_uniq (p + 5) [p+4] _ ((p + 4) :: A1) B'
          (hSdAlt ▸ hnd4) (hSdAlt.symm.trans hSe)
        rw [e1] at hL; simp at hL; subst hL
        rw [pq_true_iff] at h1; omega
      · -- b = p+3 good
        have hb : b = p + 3 := by omega
        subst hb
        obtain ⟨e1, e2⟩ := split_uniq (p + 3)
          ([p+4, p+5, p+15, p+14, p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse)
          ([p+2, p+1] ++ Y) ((p + 4) :: A1) B' (hS4d ▸ hnd4) (hS4d.symm.trans hSe)
        rw [hBe, e1, e2, ← hT1rev]
    · exfalso; rw [hS4def] at hh1; simp [ha1] at hh1
      have := (memS S4 hS4stack (p + 15) (by simp [hS4def])).2; omega
  refine ⟨?exist, ?unique⟩
  · intro T hT
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hT
    rcases hT with hT | hT
    · -- path to T1
      subst hT
      refine ⟨[S, S1, S2, S3, S4, T1], rfl, ?_, ?_⟩
      · simp
      · exact List.isChain_cons_cons.mpr ⟨eff1,
          List.isChain_cons_cons.mpr ⟨eff2,
            List.isChain_cons_cons.mpr ⟨eff3,
              List.isChain_cons_cons.mpr ⟨eff4,
                List.isChain_cons_cons.mpr ⟨eff5, List.isChain_singleton _⟩⟩⟩⟩⟩
    · -- path to T2
      subst hT
      refine ⟨[S, T2], rfl, ?_, ?_⟩
      · simp
      · exact List.isChain_cons_cons.mpr ⟨effT2, List.isChain_singleton _⟩
  · intro π hπ
    obtain ⟨hh, hl, hc⟩ := hπ
    rcases π with _ | ⟨A, rest⟩
    · simp at hh
    · simp only [List.head?_cons, Option.some.injEq] at hh; subst hh
      rcases rest with _ | ⟨B, rest2⟩
      · simp at hl; exact absurd hl hSne
      · rw [List.isChain_cons_cons] at hc
        rcases step1 B hc.1 with hB | hB
        · -- T1 branch
          subst hB
          rcases rest2 with _ | ⟨C, rest3⟩
          · simp at hl; exact absurd hl hS1ne
          · have hc2 := hc.2
            rw [List.isChain_cons_cons] at hc2
            have hC := step2 C hc2.1; subst hC
            rcases rest3 with _ | ⟨D, rest4⟩
            · simp at hl; exact absurd hl hS2ne
            · have hc3 := hc2.2
              rw [List.isChain_cons_cons] at hc3
              rcases step3 D hc3.1 with hD | hD
              · subst hD
                rcases rest4 with _ | ⟨E, rest5⟩
                · simp at hl; exact absurd hl hS3ne
                · have hc4 := hc3.2
                  rw [List.isChain_cons_cons] at hc4
                  have hE := step4 E hc4.1; subst hE
                  rcases rest5 with _ | ⟨F, rest6⟩
                  · simp at hl; exact absurd hl hS4ne
                  · have hc5 := hc4.2
                    rw [List.isChain_cons_cons] at hc5
                    have hF := step5 F hc5.1; subst hF
                    refine ⟨T1, ?_, ?_⟩
                    · simp [T1]
                    · simp
              · -- alt deadlock
                subst hD
                set Bdl := [p+13, p+12, p+11, p+8, p+7, p+6, p+9, p+10] ++ X.reverse ++
                    [p+3, p+4, p+5, p+15, p+14, p+2, p+1] ++ Y
                have hDL := deadlock_alt_fork_a p X Y hS
                have hBne : Bdl ≠ identity S.length := by
                  have hbne' : Bdl ≠ identity Bdl.length := hDL.1
                  have hlen : Bdl.length = S.length := by
                    simp [Bdl, hSdef, List.length_append, List.length_reverse]
                    omega
                  rwa [hlen] at hbne'
                rcases rest4 with _ | ⟨E, _⟩
                · simp at hl; exact absurd hl hBne
                · exact absurd (List.isChain_cons_cons.mp hc3.2).1 (hDL.2 E)
        · -- T2 branch
          subst hB
          refine ⟨T2, ?_, ?_⟩
          · simp [T2]
          · simp

end PancakeHard

theorem solution (p : ℕ) (X Y : List ℕ) :
    (PancakeHard.IsStack (PancakeHard.forkE p ++ X ++ PancakeHard.forkF p ++ Y) →
      PancakeHard.LeadsTo (PancakeHard.forkE p ++ X ++ PancakeHard.forkF p ++ Y)
        {X ++ PancakeHard.forkF1 p ++ Y, X.reverse ++ PancakeHard.forkF2 p ++ Y}) ∧
    (PancakeHard.IsStack (PancakeHard.forkF1 p ++ Y) →
      PancakeHard.LeadsTo (PancakeHard.forkF1 p ++ Y)
        {(PancakeHard.interval (p + 1) (p + 15)).reverse ++ Y}) ∧
    (PancakeHard.IsStack (PancakeHard.forkF2 p ++ Y) →
      PancakeHard.LeadsTo (PancakeHard.forkF2 p ++ Y)
        {(PancakeHard.interval (p + 1) (p + 15)).reverse ++ Y}) :=
  ⟨PancakeHard.prop7_a p X Y, PancakeHard.prop7_b p Y, PancakeHard.prop7_c p Y⟩
