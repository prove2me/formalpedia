-- Prove2me | solution 1 for SeedRecyclingDL.Codes.corollary_4_2
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T15:29:34.303002+00:00
-- url     : https://prove2.me/submissions/955c9efe-b964-49b0-af13-114ecd664e79

import Definitions.Def_SeedRecyclingDL_Codes_Execution

set_option autoImplicit false

namespace SeedRecyclingDL.Codes

theorem op_append_suffix (u v s : Word) (e : Operation) (h : applyOperation u e = some v) :
    applyOperation (u ++ s) e = some (v ++ s) := by
  cases e with
  | insert i a =>
    simp only [applyOperation] at h ⊢
    split_ifs at h with hi
    cases h
    rw [if_pos (by simp; omega)]
    simp [List.take_append_of_le_length hi, List.drop_append_of_le_length hi]
  | delete i =>
    simp only [applyOperation] at h ⊢
    split_ifs at h with hi
    cases h
    rw [if_pos (by simp; omega)]
    simp [List.take_append_of_le_length hi.le, List.drop_append_of_le_length (show i + 1 ≤ u.length by omega)]
  | substitute i a =>
    simp only [applyOperation] at h ⊢
    split_ifs at h with hi
    cases h
    rw [if_pos ⟨by simp; omega, by rw [List.getElem?_append_left hi.1]; exact hi.2⟩]
    simp [List.take_append_of_le_length hi.1.le, List.drop_append_of_le_length (show i + 1 ≤ u.length by omega)]
  | transpose i =>
    simp only [applyOperation] at h ⊢
    cases h1 : u[i]? <;> cases h2 : u[i+1]? <;> simp only [h1, h2, reduceCtorEq] at h
    rename_i a c
    have hi2 : i + 1 < u.length := (List.getElem?_eq_some_iff.mp h2).1
    rw [List.getElem?_append_left (by omega), List.getElem?_append_left hi2, h1, h2]
    cases h
    simp [List.take_append_of_le_length (show i ≤ u.length by omega),
      List.drop_append_of_le_length (show i + 2 ≤ u.length by omega)]

theorem script_append_suffix (es : List Operation) (u v s : Word) (h : applyScript es u = some v) :
    applyScript es (u ++ s) = some (v ++ s) := by
  induction es generalizing u with
  | nil => simp [applyScript] at h ⊢; rw [h]
  | cons e es ih =>
    simp only [applyScript, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨w, hw, hr⟩ := h
    exact ⟨w ++ s, op_append_suffix _ _ _ _ hw, ih _ hr⟩

theorem tk_dr1 (A B : Word) (b : Bit) : List.drop (A.length + 1) (A ++ b :: B) = B := by
  induction A <;> simp_all

theorem tk_dr2 (A B : Word) (b c : Bit) : List.drop (A.length + 2) (A ++ b :: c :: B) = B := by
  induction A with
  | nil => simp
  | cons x A ih => simpa [Nat.add_right_comm] using ih

theorem tk_g0 (A B : Word) (b : Bit) : (A ++ b :: B)[A.length]? = some b := by
  induction A <;> simp_all

theorem tk_g1 (A B : Word) (b c : Bit) : (A ++ b :: c :: B)[A.length + 1]? = some c := by
  induction A <;> simp_all

theorem split_at1 (u : Word) (i : ℕ) (hi : i < u.length) :
    ∃ A b B, u = A ++ b :: B ∧ A.length = i := by
  refine ⟨u.take i, u[i], u.drop (i+1), ?_, by simp; omega⟩
  conv_lhs => rw [← List.take_append_drop i u, ← List.cons_getElem_drop_succ (h := hi)]

theorem split_at2 (u : Word) (i : ℕ) (hi : i + 1 < u.length) :
    ∃ A b c B, u = A ++ b :: c :: B ∧ A.length = i := by
  obtain ⟨A, b, B, rfl, rfl⟩ := split_at1 u i (by omega)
  cases B with
  | nil => simp at hi
  | cons c B => exact ⟨A, b, c, B, rfl, rfl⟩

theorem op_inverse (u v : Word) (e : Operation) (h : applyOperation u e = some v) :
    ∃ e', applyOperation v e' = some u := by
  cases e with
  | insert i a =>
    simp only [applyOperation] at h
    split_ifs at h with hi
    obtain ⟨A, B, rfl, rfl⟩ : ∃ A B, u = A ++ B ∧ A.length = i :=
      ⟨u.take i, u.drop i, by simp, by simp; omega⟩
    obtain rfl := Option.some.inj h
    refine ⟨.delete A.length, ?_⟩
    simp [applyOperation, List.take_left, List.drop_left, tk_dr1]
  | delete i =>
    simp only [applyOperation] at h
    split_ifs at h with hi
    obtain ⟨A, b, B, rfl, rfl⟩ := split_at1 u i hi
    obtain rfl := Option.some.inj h
    refine ⟨.insert A.length b, ?_⟩
    simp [applyOperation, List.take_left, List.drop_left, tk_dr1]
  | substitute i a =>
    simp only [applyOperation] at h
    split_ifs at h with hi
    obtain ⟨A, b, B, rfl, rfl⟩ := split_at1 u i hi.1
    obtain rfl := Option.some.inj h
    have hab : b ≠ a := by have := hi.2; rw [tk_g0] at this; simpa using this
    refine ⟨.substitute A.length b, ?_⟩
    simp [applyOperation, List.take_left, List.drop_left, tk_dr1, tk_g0, Ne.symm hab]
  | transpose i =>
    simp only [applyOperation] at h
    split at h
    · rename_i a c h1 h2
      have hi2 : i + 1 < u.length := (List.getElem?_eq_some_iff.mp h2).1
      obtain ⟨A, b, d, B, rfl, rfl⟩ := split_at2 u i hi2
      rw [tk_g0] at h1
      rw [tk_g1] at h2
      cases h1; cases h2
      obtain rfl := Option.some.inj h
      refine ⟨.transpose A.length, ?_⟩
      simp [applyOperation, List.take_left, tk_dr2]
    · cases h

theorem script_inverse (es : List Operation) (u v : Word) (h : applyScript es u = some v) :
    ∃ fs : List Operation, fs.length ≤ es.length ∧ applyScript fs v = some u := by
  induction es generalizing u with
  | nil => simp [applyScript] at h; exact ⟨[], le_rfl, by simp [applyScript, h]⟩
  | cons e es ih =>
    simp only [applyScript, Option.bind_eq_some_iff] at h
    obtain ⟨w, hw, hr⟩ := h
    obtain ⟨fs, hfs, hfa⟩ := ih _ hr
    obtain ⟨e', he'⟩ := op_inverse _ _ _ hw
    refine ⟨fs ++ [e'], by simp; omega, ?_⟩
    simp [applyScript_append, hfa, applyScript, he']

theorem nil_or_snoc (u : Word) : u = [] ∨ ∃ w z, u = w ++ [z] := by
  rcases List.eq_nil_or_concat u with h | ⟨w, z, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨w, z, by simpa using h⟩

@[simp] theorem dl_cons (B : Word) (b z : Bit) : (b :: (B ++ [z])).dropLast = b :: B := by
  rw [← List.cons_append, List.dropLast_concat]

theorem dl_mid (A B : Word) (b z : Bit) : (A ++ b :: (B ++ [z])).dropLast = A ++ b :: B := by
  rw [← List.cons_append, ← List.append_assoc, List.dropLast_concat]

theorem op_dropLast (u v : Word) (e : Operation) (h : applyOperation u e = some v) :
    ∃ fs : List Operation, fs.length ≤ 1 ∧ applyScript fs u.dropLast = some v.dropLast := by
  rcases nil_or_snoc u with hu | ⟨w, z, hu⟩
  · subst hu
    cases e with
    | insert i a =>
      simp only [applyOperation] at h
      split_ifs at h with hi
      cases h
      refine ⟨[], by simp, ?_⟩
      simp at hi; subst hi; simp [applyScript]
    | delete i => simp [applyOperation] at h
    | substitute i a => simp [applyOperation] at h
    | transpose i => simp [applyOperation] at h
  subst hu
  rw [List.dropLast_concat]
  cases e with
  | insert i a =>
    simp only [applyOperation] at h
    split_ifs at h with hi
    obtain rfl := Option.some.inj h
    rcases Nat.lt_or_ge w.length i with hi' | hi'
    · have : i = w.length + 1 := by simp at hi; omega
      subst this
      refine ⟨[.insert w.length z], by simp, ?_⟩
      rw [List.take_of_length_le (by simp), List.drop_of_length_le (by simp)]
      simp [applyScript, applyOperation]
    · obtain ⟨A, B, rfl, rfl⟩ : ∃ A B, w = A ++ B ∧ A.length = i :=
        ⟨w.take i, w.drop i, by simp, by simp; omega⟩
      refine ⟨[.insert A.length a], by simp, ?_⟩
      simp [applyScript, applyOperation, List.take_left, List.drop_left, dl_mid]
  | delete i =>
    simp only [applyOperation] at h
    split_ifs at h with hi
    obtain rfl := Option.some.inj h
    rcases Nat.lt_or_ge i w.length with hi' | hi'
    · obtain ⟨A, b, B, rfl, rfl⟩ := split_at1 w i hi'
      refine ⟨[.delete A.length], by simp, ?_⟩
      simp [applyScript, applyOperation, List.take_left, List.drop_left, tk_dr1]
    · have : i = w.length := by simp at hi; omega
      subst this
      rw [List.take_left, List.drop_of_length_le (by simp), List.append_nil]
      rcases nil_or_snoc w with hw | ⟨w', y, hw⟩
      · subst hw; exact ⟨[], by simp, by simp [applyScript]⟩
      · subst hw
        refine ⟨[.delete w'.length], by simp, ?_⟩
        simp [applyScript, applyOperation]
  | substitute i a =>
    simp only [applyOperation] at h
    split_ifs at h with hi
    obtain rfl := Option.some.inj h
    rcases Nat.lt_or_ge i w.length with hi' | hi'
    · obtain ⟨A, b, B, rfl, rfl⟩ := split_at1 w i hi'
      have hab : ¬ b = a := by simpa [tk_g0] using hi.2
      refine ⟨[.substitute A.length a], by simp, ?_⟩
      simp [applyScript, applyOperation, List.take_left, tk_dr1, tk_g0, hab, dl_mid]
    · have : i = w.length := by simp at hi; omega
      subst this
      refine ⟨[], by simp, ?_⟩
      rw [List.take_left, List.drop_of_length_le (by simp)]
      simp [applyScript]
  | transpose i =>
    simp only [applyOperation] at h
    split at h
    · rename_i a c h1 h2
      obtain rfl := Option.some.inj h
      have hi2 : i + 1 < (w ++ [z]).length := (List.getElem?_eq_some_iff.mp h2).1
      rcases Nat.lt_or_ge (i + 1) w.length with hi' | hi'
      · obtain ⟨A, b, d, B, rfl, rfl⟩ := split_at2 w i hi'
        obtain rfl : b = a := by simpa [tk_g0] using h1
        obtain rfl : d = c := by simpa [tk_g1] using h2
        refine ⟨[.transpose A.length], by simp, ?_⟩
        simp [applyScript, applyOperation, List.take_left, tk_dr2, tk_g0, tk_g1]
      · have hiw : i + 1 = w.length := by simp at hi2; omega
        rcases nil_or_snoc w with hw | ⟨A, b, rfl⟩
        · subst hw; simp at hiw
        obtain rfl : i = A.length := by simp at hiw; omega
        obtain rfl : b = a := by simpa [tk_g0] using h1
        obtain rfl : z = c := by simpa [tk_g1] using h2
        by_cases hbz : b = z
        · subst hbz
          refine ⟨[], by simp, ?_⟩
          simp [applyScript, List.take_left, tk_dr2]
        · refine ⟨[.substitute A.length z], by simp, ?_⟩
          simp [applyScript, applyOperation, List.take_left, tk_dr1, tk_dr2, tk_g0, hbz]
    · cases h

theorem script_dropLast (es : List Operation) (u v : Word) (h : applyScript es u = some v) :
    ∃ fs : List Operation, fs.length ≤ es.length ∧ applyScript fs u.dropLast = some v.dropLast := by
  induction es generalizing u with
  | nil => simp [applyScript] at h; exact ⟨[], le_rfl, by simp [applyScript, h]⟩
  | cons e es ih =>
    simp only [applyScript, Option.bind_eq_some_iff] at h
    obtain ⟨w, hw, hr⟩ := h
    obtain ⟨fs, hfs, hfa⟩ := ih _ hr
    obtain ⟨gs, hgs, hga⟩ := op_dropLast _ _ _ hw
    refine ⟨gs ++ fs, by simp; omega, ?_⟩
    simp [applyScript_append, hga, hfa]

theorem reaches_suffix_iff (q : ℕ) (x x' s : Word) :
    Reaches q (x ++ s) (x' ++ s) ↔ Reaches q x x' := by
  constructor
  · induction s using List.reverseRecOn with
    | nil => simp
    | append_singleton s a ih =>
      rintro ⟨es, hl, hes⟩
      obtain ⟨fs, hfs, hfa⟩ := script_dropLast _ _ _ hes
      apply ih
      refine ⟨fs, by omega, ?_⟩
      simpa [← List.append_assoc] using hfa
  · rintro ⟨es, hl, hes⟩
    exact ⟨es, hl, script_append_suffix _ _ _ _ hes⟩

theorem reaches_symm (q : ℕ) (u v : Word) (h : Reaches q u v) : Reaches q v u := by
  obtain ⟨es, hl, hes⟩ := h
  obtain ⟨fs, hfs, hfa⟩ := script_inverse _ _ _ hes
  exact ⟨fs, by omega, hfa⟩

theorem reaches_trans (p q : ℕ) (u v w : Word) (h1 : Reaches p u v) (h2 : Reaches q v w) :
    Reaches (p + q) u w := by
  obtain ⟨es, hl, hes⟩ := h1
  obtain ⟨fs, hfl, hfs⟩ := h2
  exact ⟨es ++ fs, by simp; omega, by simp [applyScript_append, hes, hfs]⟩

theorem reaches_split (p q : ℕ) (u w : Word) (h : Reaches (p + q) u w) :
    ∃ v, Reaches p u v ∧ Reaches q v w := by
  obtain ⟨es, hl, hes⟩ := h
  rw [← List.take_append_drop p es, applyScript_append] at hes
  cases hv : applyScript (es.take p) u with
  | none => simp [hv] at hes
  | some v =>
    rw [hv] at hes
    refine ⟨v, ⟨es.take p, by simp, hv⟩, ⟨es.drop p, by simp; omega, by simpa using hes⟩⟩

end SeedRecyclingDL.Codes

open SeedRecyclingDL.Codes

theorem solution (t m N : ℕ) :
    (∀ x x' s : Word, x.length = m → x'.length = m → s.length = N →
      distance (x ++ s) (x' ++ s) = distance x x') ∧
    (∀ x : Word, x.length = m → payloadCompetitors (dlChannel t) m N x = dlCompetitors t m x) := by
  classical
  constructor
  · intro x x' s _ _ _
    unfold distance
    apply le_antisymm
    · exact Nat.find_min' _ ((reaches_suffix_iff _ x x' s).mpr (Nat.find_spec (pair_reachable x x')))
    · exact Nat.find_min' _ ((reaches_suffix_iff _ x x' s).mp (Nat.find_spec (pair_reachable _ _)))
  · intro x hx
    ext x'
    simp only [payloadCompetitors, dlCompetitors, Set.mem_ofPred_eq, Confusable, dlChannel, ball]
    constructor
    · rintro ⟨h1, h2, s, _, y, hy1, hy2⟩
      refine ⟨h1, h2, ?_⟩
      have := reaches_trans _ _ _ _ _ hy1 (reaches_symm _ _ _ hy2)
      rw [reaches_suffix_iff, ← two_mul] at this
      exact this
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, List.replicate N 0, by simp, ?_⟩
      rw [two_mul, ← reaches_suffix_iff _ _ _ (List.replicate N 0)] at h3
      obtain ⟨y, hy1, hy2⟩ := reaches_split _ _ _ _ h3
      exact ⟨y, hy1, reaches_symm _ _ _ hy2⟩

