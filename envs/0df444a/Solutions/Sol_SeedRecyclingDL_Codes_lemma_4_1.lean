-- Prove2me | solution 1 for SeedRecyclingDL.Codes.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-23T23:51:51.776808+00:00
-- url     : https://prove2.me/submissions/4f07ede6-023b-40a5-9823-269bdb4d79e9

import Definitions.Def_SeedRecyclingDL_Codes_Execution

set_option autoImplicit false

open SeedRecyclingDL.Codes

theorem sol41_refl (u : Word) : Reaches 0 u u := ⟨[], le_refl _, rfl⟩

theorem sol41_mono {a b : ℕ} {u v : Word} (hab : a ≤ b) (h : Reaches a u v) :
    Reaches b u v := by
  obtain ⟨es, hl, he⟩ := h
  exact ⟨es, hl.trans hab, he⟩

theorem sol41_trans {a b : ℕ} {u v w : Word} (h1 : Reaches a u v) (h2 : Reaches b v w) :
    Reaches (a + b) u w := by
  obtain ⟨es, hl, he⟩ := h1
  obtain ⟨fs, hl2, hf⟩ := h2
  refine ⟨es ++ fs, by rw [List.length_append]; omega, ?_⟩
  rw [applyScript_append, he]
  simpa using hf

theorem sol41_one {u v : Word} (e : Operation) (h : applyOperation u e = some v) :
    Reaches 1 u v :=
  ⟨[e], le_refl _, by simp [applyScript, h]⟩

/-- The four kinds of local edits, written as a replacement of a block X by a block Y. -/
def sol41_Local (X Y : Word) : Prop :=
  (X = [] ∧ ∃ a, Y = [a]) ∨ (∃ a, X = [a] ∧ Y = []) ∨
  (∃ a b, a ≠ b ∧ X = [a] ∧ Y = [b]) ∨ (∃ a c, X = [a, c] ∧ Y = [c, a])

theorem sol41_ctx (P X Y S : Word) (h : sol41_Local X Y) :
    Reaches 1 (P ++ X ++ S) (P ++ Y ++ S) := by
  rcases h with ⟨rfl, a, rfl⟩ | ⟨a, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩ | ⟨a, c, rfl, rfl⟩
  · apply sol41_one (Operation.insert P.length a)
    simp [applyOperation]
  · apply sol41_one (Operation.delete P.length)
    simp [applyOperation, List.drop_length_add_append]
  · apply sol41_one (Operation.substitute P.length b)
    simp [applyOperation, hab, List.drop_length_add_append]
  · apply sol41_one (Operation.transpose P.length)
    simp [applyOperation, List.drop_length_add_append]

theorem sol41_decomp {u v : Word} (e : Operation) (h : applyOperation u e = some v) :
    ∃ P X Y S, u = P ++ X ++ S ∧ v = P ++ Y ++ S ∧ sol41_Local X Y := by
  cases e with
  | insert i a =>
    simp only [applyOperation] at h
    split_ifs at h with hi
    injection h with h
    subst h
    exact ⟨u.take i, [], [a], u.drop i, by simp, by simp, Or.inl ⟨rfl, a, rfl⟩⟩
  | delete i =>
    simp only [applyOperation] at h
    split_ifs at h with hi
    injection h with h
    subst h
    refine ⟨u.take i, [u[i]], [], u.drop (i + 1), ?_, by simp,
      Or.inr (Or.inl ⟨_, rfl, rfl⟩)⟩
    calc u = u.take i ++ u.drop i := (List.take_append_drop i u).symm
      _ = _ := by rw [List.drop_eq_getElem_cons hi]; simp
  | substitute i a =>
    simp only [applyOperation] at h
    split_ifs at h with hi
    injection h with h
    subst h
    obtain ⟨hlt, hne⟩ := hi
    refine ⟨u.take i, [u[i]], [a], u.drop (i + 1), ?_, by simp,
      Or.inr (Or.inr (Or.inl ⟨u[i], a, ?_, rfl, rfl⟩))⟩
    · calc u = u.take i ++ u.drop i := (List.take_append_drop i u).symm
        _ = _ := by rw [List.drop_eq_getElem_cons hlt]; simp
    · intro heq
      apply hne
      rw [List.getElem?_eq_getElem hlt, heq]
  | transpose i =>
    simp only [applyOperation] at h
    cases ha : u[i]? with
    | none => simp [ha] at h
    | some a =>
      cases hc : u[i + 1]? with
      | none => simp [ha, hc] at h
      | some c =>
        simp only [ha, hc] at h
        injection h with h
        subst h
        obtain ⟨h0, ha'⟩ := List.getElem?_eq_some_iff.mp ha
        obtain ⟨h1, hc'⟩ := List.getElem?_eq_some_iff.mp hc
        have hd : u.drop i = a :: c :: u.drop (i + 1 + 1) := by
          rw [List.drop_eq_getElem_cons h0, List.drop_eq_getElem_cons h1, ha', hc']
        refine ⟨u.take i, [a, c], [c, a], u.drop (i + 2), ?_, by simp,
          Or.inr (Or.inr (Or.inr ⟨a, c, rfl, rfl⟩))⟩
        calc u = u.take i ++ u.drop i := (List.take_append_drop i u).symm
          _ = _ := by rw [hd]; simp

theorem sol41_local_len {X Y : Word} (hL : sol41_Local X Y) :
    X.length ≤ Y.length + 1 ∧ Y.length ≤ X.length + 1 := by
  rcases hL with ⟨rfl, a, rfl⟩ | ⟨a, rfl, rfl⟩ | ⟨a, b, -, rfl, rfl⟩ | ⟨a, c, rfl, rfl⟩ <;> simp

theorem sol41_local_two {X Y : Word} (hL : sol41_Local X Y) (hY : 2 ≤ Y.length) :
    ∃ a c, X = [a, c] ∧ Y = [c, a] := by
  rcases hL with ⟨rfl, a, rfl⟩ | ⟨a, rfl, rfl⟩ | ⟨a, b, -, rfl, rfl⟩ | ⟨a, c, rfl, rfl⟩
  · simp at hY
  · simp at hY
  · simp at hY
  · exact ⟨a, c, rfl, rfl⟩

theorem sol41_left_step (P X Y S : Word) (hL : sol41_Local X Y) (j1 : ℕ)
    (hj1 : j1 ≤ (P ++ Y ++ S).length) :
    ∃ j ≤ (P ++ X ++ S).length, ∃ a b, a + b ≤ 1 ∧
      Reaches a ((P ++ X ++ S).take j) ((P ++ Y ++ S).take j1) ∧
      (P ++ X ++ S).length - j ≤ (P ++ Y ++ S).length - j1 + b ∧
      (P ++ Y ++ S).length - j1 ≤ (P ++ X ++ S).length - j + b := by
  have hlen := sol41_local_len hL
  have eX : (P ++ X ++ S).length = P.length + X.length + S.length := by
    simp only [List.length_append]
  have eY : (P ++ Y ++ S).length = P.length + Y.length + S.length := by
    simp only [List.length_append]
  rw [eY] at hj1
  rw [eX, eY]
  by_cases hA : j1 ≤ P.length
  · refine ⟨j1, by omega, 0, 1, by omega, ?_, by omega, by omega⟩
    rw [List.append_assoc, List.append_assoc, List.take_append_of_le_length hA,
      List.take_append_of_le_length hA]
    exact sol41_refl _
  by_cases hB : P.length + Y.length ≤ j1
  · obtain ⟨r, rfl⟩ : ∃ r, j1 = P.length + Y.length + r :=
      ⟨j1 - (P.length + Y.length), by omega⟩
    refine ⟨P.length + X.length + r, by omega, 1, 0, by omega, ?_, by omega, by omega⟩
    have e1 : (P ++ X ++ S).take (P.length + X.length + r) = P ++ X ++ S.take r := by
      rw [show P.length + X.length + r = (P ++ X).length + r by simp,
        List.take_length_add_append]
    have e2 : (P ++ Y ++ S).take (P.length + Y.length + r) = P ++ Y ++ S.take r := by
      rw [show P.length + Y.length + r = (P ++ Y).length + r by simp,
        List.take_length_add_append]
    rw [e1, e2]
    exact sol41_ctx P X Y (S.take r) hL
  obtain ⟨a, c, rfl, rfl⟩ := sol41_local_two hL (by omega)
  have hj : j1 = P.length + 1 := by simp at hA hB; omega
  subst hj
  refine ⟨P.length + 1, by simp; omega, 1, 0, by omega, ?_, by simp, by simp⟩
  have e1 : (P ++ [a, c] ++ S).take (P.length + 1) = P ++ [a] ++ [] := by
    rw [List.append_assoc, List.take_length_add_append]; simp
  have e2 : (P ++ [c, a] ++ S).take (P.length + 1) = P ++ [c] ++ [] := by
    rw [List.append_assoc, List.take_length_add_append]; simp
  rw [e1, e2]
  by_cases hac : a = c
  · subst hac
    exact sol41_mono (by omega) (sol41_refl _)
  · exact sol41_ctx P [a] [c] [] (Or.inr (Or.inr (Or.inl ⟨a, c, hac, rfl, rfl⟩)))

theorem sol41_right_step (P X Y S : Word) (hL : sol41_Local X Y) (j1 : ℕ)
    (hj1 : j1 ≤ (P ++ Y ++ S).length) :
    ∃ j ≤ (P ++ X ++ S).length, ∃ a b, a + b ≤ 1 ∧
      Reaches a ((P ++ X ++ S).drop j) ((P ++ Y ++ S).drop j1) ∧
      j ≤ j1 + b ∧ j1 ≤ j + b := by
  have hlen := sol41_local_len hL
  have eX : (P ++ X ++ S).length = P.length + X.length + S.length := by
    simp only [List.length_append]
  have eY : (P ++ Y ++ S).length = P.length + Y.length + S.length := by
    simp only [List.length_append]
  rw [eY] at hj1
  rw [eX]
  by_cases hA : j1 ≤ P.length
  · refine ⟨j1, by omega, 1, 0, by omega, ?_, by omega, by omega⟩
    rw [List.append_assoc, List.append_assoc, List.drop_append_of_le_length hA,
      List.drop_append_of_le_length hA, ← List.append_assoc, ← List.append_assoc]
    exact sol41_ctx _ X Y S hL
  by_cases hB : P.length + Y.length ≤ j1
  · obtain ⟨r, rfl⟩ : ∃ r, j1 = P.length + Y.length + r :=
      ⟨j1 - (P.length + Y.length), by omega⟩
    refine ⟨P.length + X.length + r, by omega, 0, 1, by omega, ?_, by omega, by omega⟩
    rw [show P.length + X.length + r = (P ++ X).length + r by simp,
      List.drop_length_add_append,
      show P.length + Y.length + r = (P ++ Y).length + r by simp,
      List.drop_length_add_append]
    exact sol41_refl _
  obtain ⟨a, c, rfl, rfl⟩ := sol41_local_two hL (by omega)
  have hj : j1 = P.length + 1 := by simp at hA hB; omega
  subst hj
  refine ⟨P.length + 1, by simp; omega, 1, 0, by omega, ?_, by omega, by omega⟩
  have e1 : (P ++ [a, c] ++ S).drop (P.length + 1) = [] ++ [c] ++ S := by
    rw [List.append_assoc, List.drop_length_add_append]; simp
  have e2 : (P ++ [c, a] ++ S).drop (P.length + 1) = [] ++ [a] ++ S := by
    rw [List.append_assoc, List.drop_length_add_append]; simp
  rw [e1, e2]
  by_cases hac : c = a
  · subst hac
    exact sol41_mono (by omega) (sol41_refl _)
  · exact sol41_ctx [] [c] [a] S (Or.inr (Or.inr (Or.inl ⟨c, a, hac, rfl, rfl⟩)))

theorem sol41_left (es : List Operation) : ∀ u v : Word, applyScript es u = some v →
    ∀ j' ≤ v.length, ∃ j ≤ u.length, ∃ a b, a + b ≤ es.length ∧
      Reaches a (u.take j) (v.take j') ∧ u.length - j ≤ v.length - j' + b ∧
      v.length - j' ≤ u.length - j + b := by
  induction es with
  | nil =>
    intro u v h j' hj'
    simp only [applyScript, Option.some.injEq] at h
    subst h
    exact ⟨j', hj', 0, 0, le_refl _, sol41_refl _, by omega, by omega⟩
  | cons e es ih =>
    intro u v h j' hj'
    simp only [applyScript] at h
    cases hu1 : applyOperation u e with
    | none => simp [hu1] at h
    | some u1 =>
      simp only [hu1, Option.bind_some] at h
      obtain ⟨j1, hj1, a1, b1, hab1, hr1, hl1, hl2⟩ := ih u1 v h j' hj'
      obtain ⟨P, X, Y, S, rfl, rfl, hL⟩ := sol41_decomp e hu1
      obtain ⟨j, hj, a2, b2, hab2, hr2, hl3, hl4⟩ := sol41_left_step P X Y S hL j1 hj1
      refine ⟨j, hj, a2 + a1, b2 + b1, by rw [List.length_cons]; omega,
        sol41_trans hr2 hr1, by omega, by omega⟩

theorem sol41_right (es : List Operation) : ∀ u v : Word, applyScript es u = some v →
    ∀ j' ≤ v.length, ∃ j ≤ u.length, ∃ a b, a + b ≤ es.length ∧
      Reaches a (u.drop j) (v.drop j') ∧ j ≤ j' + b ∧ j' ≤ j + b := by
  induction es with
  | nil =>
    intro u v h j' hj'
    simp only [applyScript, Option.some.injEq] at h
    subst h
    exact ⟨j', hj', 0, 0, le_refl _, sol41_refl _, by omega, by omega⟩
  | cons e es ih =>
    intro u v h j' hj'
    simp only [applyScript] at h
    cases hu1 : applyOperation u e with
    | none => simp [hu1] at h
    | some u1 =>
      simp only [hu1, Option.bind_some] at h
      obtain ⟨j1, hj1, a1, b1, hab1, hr1, hl1, hl2⟩ := ih u1 v h j' hj'
      obtain ⟨P, X, Y, S, rfl, rfl, hL⟩ := sol41_decomp e hu1
      obtain ⟨j, hj, a2, b2, hab2, hr2, hl3, hl4⟩ := sol41_right_step P X Y S hL j1 hj1
      refine ⟨j, hj, a2 + a1, b2 + b1, by rw [List.length_cons]; omega,
        sol41_trans hr2 hr1, by omega, by omega⟩

theorem sol41_dist_le {u v : Word} {k : ℕ} (h : Reaches k u v) : distance u v ≤ k := by
  classical
  unfold distance
  exact Nat.find_min' _ h

theorem sol41_dist_spec (u v : Word) : Reaches (distance u v) u v := by
  classical
  unfold distance
  exact Nat.find_spec (pair_reachable u v)

theorem sol41_append_reach (Q : Word) : ∀ P : Word, Reaches Q.length P (P ++ Q) := by
  induction Q with
  | nil => intro P; simpa using sol41_refl P
  | cons q Q ih =>
    intro P
    have h1 : Reaches 1 P (P ++ [q]) := by
      simpa using sol41_ctx P [] [q] [] (Or.inl ⟨rfl, q, rfl⟩)
    have h2 := sol41_trans h1 (ih (P ++ [q]))
    rw [show P ++ q :: Q = P ++ [q] ++ Q by simp,
      show (q :: Q).length = 1 + Q.length by rw [List.length_cons]; omega]
    exact h2

theorem sol41_drop_suffix (Q : Word) : ∀ P : Word, Reaches Q.length (P ++ Q) P := by
  induction Q with
  | nil => intro P; simpa using sol41_refl P
  | cons q Q ih =>
    intro P
    have h1 : Reaches 1 (P ++ [q] ++ Q) (P ++ Q) := by
      simpa using sol41_ctx P [q] [] Q (Or.inr (Or.inl ⟨q, rfl, rfl⟩))
    have h2 := sol41_trans h1 (ih P)
    rw [show P ++ q :: Q = P ++ [q] ++ Q by simp,
      show (q :: Q).length = 1 + Q.length by rw [List.length_cons]; omega]
    exact h2

theorem sol41_prefix_reach (Q S : Word) : Reaches Q.length S (Q ++ S) := by
  induction Q with
  | nil => simpa using sol41_refl S
  | cons q Q ih =>
    have h1 : Reaches 1 (Q ++ S) (q :: (Q ++ S)) := by
      simpa using sol41_ctx [] [] [q] (Q ++ S) (Or.inl ⟨rfl, q, rfl⟩)
    have h2 := sol41_trans ih h1
    rw [List.cons_append, List.length_cons]
    exact h2

theorem sol41_drop_prefix (Q S : Word) : Reaches Q.length (Q ++ S) S := by
  induction Q with
  | nil => simpa using sol41_refl S
  | cons q Q ih =>
    have h1 : Reaches 1 (q :: (Q ++ S)) (Q ++ S) := by
      simpa using sol41_ctx [] [q] [] (Q ++ S) (Or.inr (Or.inl ⟨q, rfl, rfl⟩))
    have h2 := sol41_trans h1 ih
    rw [List.cons_append, show (q :: Q).length = 1 + Q.length by rw [List.length_cons]; omega]
    exact h2

theorem solution (m N : ℕ) (x x' s s' : Word)
    (hx : x.length = m) (hx' : x'.length = m)
    (hs : s.length = N) (hs' : s'.length = N) :
    max (distance x x') (distance s s') ≤ distance (x ++ s) (x' ++ s') := by
  obtain ⟨es, hes, happ⟩ := sol41_dist_spec (x ++ s) (x' ++ s')
  apply max_le
  · obtain ⟨j, hj, a, b, hab, hr, hl1, hl2⟩ :=
      sol41_left es (x ++ s) (x' ++ s') happ m (by rw [List.length_append]; omega)
    rw [List.take_left' hx'] at hr
    simp only [List.length_append] at hj hl1 hl2
    have hpre : Reaches b x ((x ++ s).take j) := by
      by_cases hjm : j ≤ m
      · rw [List.take_append_of_le_length (by omega)]
        have h := sol41_drop_suffix (x.drop j) (x.take j)
        rw [List.take_append_drop] at h
        exact sol41_mono (by rw [List.length_drop]; omega) h
      · rw [List.take_append, hx, List.take_of_length_le (by omega)]
        exact sol41_mono (by rw [List.length_take]; omega) (sol41_append_reach _ x)
    exact (sol41_dist_le (sol41_trans hpre hr)).trans (by omega)
  · obtain ⟨j, hj, a, b, hab, hr, hl1, hl2⟩ :=
      sol41_right es (x ++ s) (x' ++ s') happ m (by rw [List.length_append]; omega)
    rw [List.drop_left' hx'] at hr
    simp only [List.length_append] at hj
    have hpre : Reaches b s ((x ++ s).drop j) := by
      by_cases hjm : j ≤ m
      · rw [List.drop_append_of_le_length (by omega)]
        exact sol41_mono (by rw [List.length_drop]; omega) (sol41_prefix_reach (x.drop j) s)
      · rw [List.drop_append, hx, List.drop_of_length_le (by omega), List.nil_append]
        have h := sol41_drop_prefix (s.take (j - m)) (s.drop (j - m))
        rw [List.take_append_drop] at h
        exact sol41_mono (by rw [List.length_take]; omega) h
    exact (sol41_dist_le (sol41_trans hpre hr)).trans (by omega)
