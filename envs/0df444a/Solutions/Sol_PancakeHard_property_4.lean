-- Prove2me | solution 1 for PancakeHard.property_4
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-04T15:20:51.412187+00:00
-- url     : https://prove2.me/submissions/7e8dda0e-a806-407a-bab4-a4e1a8fe6776

import Mathlib
import Definitions.Def_PancakeHard_Dock

set_option autoImplicit false

namespace PancakeHard

private def pq (xy : ℕ × ℕ) : Bool := !(xy.1 + 1 == xy.2 || xy.2 + 1 == xy.1)

private def cc (L : List ℕ) : ℕ := (L.zip L.tail).countP pq

private lemma pq_symm (a b : ℕ) : pq (a, b) = pq (b, a) := by
  unfold pq; cases h1 : (a + 1 == b) <;> cases h2 : (b + 1 == a) <;> simp_all

private lemma cc_nil : cc [] = 0 := rfl
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
    | cons a' A'' =>
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
    intro h0
    rw [List.take_eq_nil_iff] at h0
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
    cases h1 : pq (aL, b) <;> cases h2 : pq (a1, b) <;> simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at key ⊢ <;> first | (exfalso; omega) | simp
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

private lemma int_cons (a b : ℕ) (h : a ≤ b) : interval a b = a :: interval (a + 1) b := by
  unfold interval
  rw [show b + 1 - a = (b + 1 - (a + 1)) + 1 by omega, List.range'_succ]

private lemma int_snoc (a b : ℕ) (h : a ≤ b) (hb : 1 ≤ b) : interval a b = interval a (b - 1) ++ [b] := by
  unfold interval
  rw [show b + 1 - a = (b - 1 + 1 - a) + 1 by omega, List.range'_concat]
  congr 2; omega

private lemma int_empty (a b : ℕ) (h : b < a) : interval a b = [] := by
  unfold interval; rw [show b + 1 - a = 0 by omega]; rfl

private lemma pq_false_iff (a b : ℕ) : pq (a, b) = false ↔ (a + 1 = b ∨ b + 1 = a) := by
  unfold pq; cases h1 : (a + 1 == b) <;> cases h2 : (b + 1 == a) <;> simp_all

private lemma pq_true_iff (a b : ℕ) : pq (a, b) = true ↔ ¬(a + 1 = b ∨ b + 1 = a) := by
  unfold pq; cases h1 : (a + 1 == b) <;> cases h2 : (b + 1 == a) <;> simp_all

theorem p4_aux (p q : ℕ) (X Y : List ℕ) (hpq : p < q)
    (hS : IsStack ((interval (p + 1) q).reverse ++ X ++ Dock p q ++ Y)) :
    LeadsTo ((interval (p + 1) q).reverse ++ X ++ Dock p q ++ Y)
      {X ++ interval (p - 1) (q + 2) ++ Y} := by
  set S := (interval (p + 1) q).reverse ++ X ++ Dock p q ++ Y with hSdef
  have hnd := stack_nodup S hS
  have hmem := memS S hS
  have hp2 : 2 ≤ p := by
    have := (hmem (p - 1) (by simp [hSdef, Dock])).1; omega
  have hqn : q + 2 ≤ S.length := (hmem (q + 2) (by simp [hSdef, Dock])).2
  set I0 := interval (p + 1) (q - 1) with hI0
  set J := interval (p + 2) q with hJ
  have hI2 : interval (p + 1) q = I0 ++ [q] := int_snoc _ _ (by omega) (by omega)
  have hI1 : interval (p + 1) q = (p + 1) :: J := int_cons _ _ (by omega)
  have hkey : ∀ Z : List ℕ, I0 ++ q :: Z = (p + 1) :: (J ++ Z) := by
    intro Z
    have := congrArg (· ++ Z) (hI2.symm.trans hI1)
    simpa using this
  set M := I0.reverse ++ X ++ [p - 1, p] with hM
  have hSd : S = (q :: M) ++ (q + 1) :: (q + 2) :: Y := by
    rw [hSdef, hI2, hM]; simp [Dock]
  set S1 := (p :: (p - 1) :: X.reverse) ++ (p + 1) :: (J ++ (q + 1) :: (q + 2) :: Y) with hS1def
  have hS1eq : (q :: M).reverse ++ (q + 1) :: (q + 2) :: Y = S1 := by
    rw [hS1def, hM]; simp [hkey]
  set T := X ++ interval (p - 1) (q + 2) ++ Y with hTdef
  have hTeq : (p :: (p - 1) :: X.reverse).reverse ++ (p + 1) :: (J ++ (q + 1) :: (q + 2) :: Y) = T := by
    rw [hTdef, int_cons (p - 1) (q + 2) (by omega), show p - 1 + 1 = p by omega,
      int_cons p (q + 2) (by omega), int_cons (p + 1) (q + 2) (by omega),
      int_snoc (p + 1 + 1) (q + 2) (by omega) (by omega),
      int_snoc (p + 1 + 1) (q + 2 - 1) (by omega) (by omega),
      show p + 1 + 1 = p + 2 by omega, show q + 2 - 1 - 1 = q by omega,
      show q + 2 - 1 = q + 1 by omega, ← hJ]
    simp
  have hXf : ∀ x ∈ X, x ≠ p ∧ x ≠ p + 2 := by
    intro x hx
    have e1 : S = ((interval (p + 1) q).reverse ++ X) ++ (Dock p q ++ Y) := by simp [hSdef]
    have e2 : S = (interval (p + 1) q).reverse ++ (X ++ Dock p q ++ Y) := by simp [hSdef]
    have d1 := (List.nodup_append.mp (e1 ▸ hnd)).2.2
    have d2 := (List.nodup_append.mp (e2 ▸ hnd)).2.2
    refine ⟨fun h => d1 x (by simp [hx]) p (by simp [Dock]) h, fun h => ?_⟩
    by_cases hq : p + 2 ≤ q
    · exact d2 (p + 2) (by simp [interval, List.mem_range'_1]; omega) x (by simp [hx]) h.symm
    · exact d1 x (by simp [hx]) (p + 2) (by simp [Dock]; omega) h
  have eff1 : EfficientFlip S S1 := by
    have := eff_of q M p (List.getLast?_eq_some_iff.mpr ⟨q :: (I0.reverse ++ X ++ [p - 1]), by simp [hM]⟩) (q + 1) ((q + 2) :: Y)
      (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
    rw [← hSd, hS1eq] at this; exact this
  have eff2 : EfficientFlip S1 T := by
    rw [← hTeq, hS1def]
    obtain hX | ⟨x, X', hX⟩ : X = [] ∨ ∃ x X', X = x :: X' := by cases X <;> simp
    · rw [hX]
      exact eff_of p [p - 1] (p - 1) (by simp) (p + 1) _ (by rw [pq_true_iff]; omega)
        (by rw [pq_false_iff]; omega)
    · have hx := hXf x (by rw [hX]; simp)
      rw [hX]
      exact eff_of p ((p - 1) :: (x :: X').reverse) x
        (List.getLast?_eq_some_iff.mpr ⟨p :: (p - 1) :: X'.reverse, by simp⟩) (p + 1) _
        (by rw [pq_true_iff]; omega) (by rw [pq_false_iff]; omega)
  have hperm : S1.Perm S := by
    rw [← hS1eq, hSd]; exact (List.reverse_perm _).append_right _
  have hlen1 : S1.length = S.length := hperm.length_eq
  have hS1 : IsStack S1 := by unfold IsStack; rw [hlen1]; exact hperm.trans hS
  have hnd1 := stack_nodup S1 hS1
  have step1 : ∀ B, EfficientFlip S B → B = S1 := by
    intro B hB
    rcases eff_char S B hB with ⟨a1, A1, aL, b, B', hL, hSe, hBe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : q = a1 := by
        have := congrArg List.head? (hSd.symm.trans hSe); simpa using this
      subst ha1
      rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · subst h2
        obtain ⟨e1, e2⟩ := split_uniq (q + 1) (q :: M) ((q + 2) :: Y) (q :: A1) B'
          (hSd ▸ hnd) (hSd.symm.trans hSe)
        rw [hBe, e1, e2, hS1eq]
      · by_cases hq : p + 2 ≤ q
        · have hI0' : I0 = interval (p + 1) (q - 1 - 1) ++ [q - 1] := int_snoc _ _ (by omega) (by omega)
          have hSd2 : S = [q] ++ (q - 1) :: ((interval (p + 1) (q - 1 - 1)).reverse ++ X ++
              [p - 1, p, q + 1, q + 2] ++ Y) := by
            rw [hSd, hM, hI0']; simp
          have hb : b = q - 1 := by omega
          subst hb
          obtain ⟨e1, -⟩ := split_uniq (q - 1) [q] _ (q :: A1) B' (hSd2 ▸ hnd) (hSd2.symm.trans hSe)
          rw [e1] at hL; simp at hL; subst hL
          rw [pq_true_iff] at h1; omega
        · have hI0e : I0 = [] := int_empty _ _ (by omega)
          have hSd2 : S = (q :: (X ++ [p - 1])) ++ p :: (q + 1) :: (q + 2) :: Y := by
            rw [hSd, hM, hI0e]; simp
          have hb : b = p := by omega
          rw [hb] at hSe h1
          obtain ⟨e1, -⟩ := split_uniq p _ _ (q :: A1) B' (hSd2 ▸ hnd) (hSd2.symm.trans hSe)
          have hl2 : (q :: (X ++ [p - 1])).getLast? = some (p - 1) :=
            List.getLast?_eq_some_iff.mpr ⟨q :: X, by simp⟩
          rw [e1, hl2] at hL
          injection hL with hL
          rw [← hL, pq_true_iff] at h1; omega
    · exfalso; rw [hSd] at hh1; simp at hh1; omega
  have step2 : ∀ C, EfficientFlip S1 C → C = T := by
    intro C hC
    rcases eff_char S1 C hC with ⟨a1, A1, aL, b, B', hL, hSe, hCe, h1, h2⟩ | ⟨a1, hh1, ha1⟩
    · have ha1 : p = a1 := by
        have := congrArg List.head? (hS1def.symm.trans hSe); simpa using this
      subst ha1
      rw [pq_false_iff] at h2
      rcases h2 with h2 | h2
      · subst h2
        obtain ⟨e1, e2⟩ := split_uniq (p + 1) (p :: (p - 1) :: X.reverse)
          (J ++ (q + 1) :: (q + 2) :: Y) (p :: A1) B' (hS1def ▸ hnd1) (hS1def.symm.trans hSe)
        rw [hCe, e1, e2, hTeq]
      · have hSd2 : S1 = [p] ++ (p - 1) :: (X.reverse ++ (p + 1) :: (J ++ (q + 1) :: (q + 2) :: Y)) := by
          rw [hS1def]; simp
        have hb : b = p - 1 := by omega
        subst hb
        obtain ⟨e1, -⟩ := split_uniq (p - 1) [p] _ (p :: A1) B' (hSd2 ▸ hnd1) (hSd2.symm.trans hSe)
        rw [e1] at hL; simp at hL; subst hL
        rw [pq_true_iff] at h1; omega
    · exfalso; rw [hS1def] at hh1; simp at hh1; omega
  have hSne : S ≠ identity S.length := by
    intro h
    have := congrArg List.head? h
    rw [identity_head _ (by omega), hSd] at this; simp at this; omega
  have hS1ne : S1 ≠ identity S.length := by
    intro h
    have := congrArg List.head? h
    rw [identity_head _ (by omega), hS1def] at this; simp at this; omega
  refine ⟨?_, ?_⟩
  · intro T' hT'
    rw [Set.mem_singleton_iff] at hT'
    subst hT'
    exact ⟨[S, S1, T], rfl, rfl, List.isChain_cons_cons.mpr ⟨eff1,
      List.isChain_cons_cons.mpr ⟨eff2, List.isChain_singleton _⟩⟩⟩
  · intro π hπ
    obtain ⟨hh, hl, hc⟩ := hπ
    rcases π with _ | ⟨A, _ | ⟨B, rest⟩⟩
    · simp at hh
    · simp at hh hl; exact absurd (hh ▸ hl) hSne
    · simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      rw [List.isChain_cons_cons] at hc
      have hB := step1 B hc.1
      subst hB
      rcases rest with _ | ⟨C, rest'⟩
      · simp at hl; exact absurd hl hS1ne
      · rw [List.isChain_cons_cons] at hc
        have hC := step2 C hc.2.1
        subst hC
        exact ⟨_, rfl, by simp⟩

end PancakeHard

theorem solution (p q : ℕ) (X Y : List ℕ) (hpq : p < q)
    (hS : PancakeHard.IsStack ((PancakeHard.interval (p + 1) q).reverse ++ X ++ PancakeHard.Dock p q ++ Y)) :
    PancakeHard.LeadsTo ((PancakeHard.interval (p + 1) q).reverse ++ X ++ PancakeHard.Dock p q ++ Y)
      {X ++ PancakeHard.interval (p - 1) (q + 2) ++ Y} :=
  PancakeHard.p4_aux p q X Y hpq hS
