-- Prove2me | solution 1 for SecSampling.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:17:24.715222+00:00
-- url     : https://prove2.me/submissions/1f553965-63d6-4ade-b016-57ee6d34660a

import Mathlib
import Definitions.Def_SecSampling_ConflictGraph

namespace Aux_SecSampling_lemma_9

open SecSampling

theorem ct_false_cons (l : List Bool) : List.count true (false :: l) = List.count true l :=
  List.count_cons_of_ne (by decide)

theorem cf_false_cons (l : List Bool) : List.count false (false :: l) = List.count false l + 1 :=
  List.count_cons_self

theorem ct_of_nf (l : List Bool) (h : false ∉ l) : l.count true = l.length :=
  List.count_eq_length.mpr (fun b hb => by
    cases b
    · exact absurd hb h
    · rfl)

theorem ct_add_cf (l : List Bool) : l.count true + l.count false = l.length := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b
    · rw [ct_false_cons, cf_false_cons, List.length_cons]; omega
    · rw [List.count_cons_self, List.count_cons_of_ne (by decide), List.length_cons]; omega

theorem all_of_nf (l : List Bool) (h : false ∉ l) : ∀ b ∈ l, b = true := fun b hb => by
  cases b
  · exact absurd hb h
  · rfl

theorem eq_of_nf (A B : List Bool) (hA : false ∉ A) (hB : false ∉ B)
    (hl : A.length = B.length) : A = B := by
  have e1 : A = List.replicate A.length true := List.eq_replicate_iff.mpr ⟨rfl, all_of_nf A hA⟩
  have e2 : B = List.replicate B.length true := List.eq_replicate_iff.mpr ⟨rfl, all_of_nf B hB⟩
  calc A = List.replicate A.length true := e1
    _ = List.replicate B.length true := by rw [hl]
    _ = B := e2.symm

theorem idx_lemma (T R : List Bool) (h : false ∉ T) :
    (T ++ false :: R).idxOf false = T.length := by
  rw [List.idxOf_append, if_neg h, List.idxOf_cons_self]
  omega

theorem lz_eq (P T : List Bool) (hT : false ∉ T) : lastZero (P ++ false :: T) = P.length + 1 := by
  unfold lastZero
  rw [if_pos (show false ∈ P ++ false :: T by simp)]
  have hrev : (P ++ false :: T).reverse = T.reverse ++ false :: P.reverse := by simp
  have hT' : false ∉ T.reverse := by rw [List.mem_reverse]; exact hT
  rw [hrev, idx_lemma _ _ hT']
  simp only [List.length_append, List.length_cons, List.length_reverse]
  omega

theorem decomp (I : List Bool) (h : false ∈ I) : ∃ P T, false ∉ T ∧ I = P ++ false :: T := by
  induction I with
  | nil => simp at h
  | cons a I ih =>
    by_cases h' : false ∈ I
    · obtain ⟨P, T, hT, hI⟩ := ih h'
      exact ⟨a :: P, T, hT, by rw [hI, List.cons_append]⟩
    · have ha : a = false := by
        rcases List.mem_cons.mp h with h1 | h1
        · exact h1.symm
        · exact absurd h1 h'
      exact ⟨[], I, h', by rw [ha, List.nil_append]⟩

theorem ins_lemma (L M : List Bool) (x : Bool) : (L ++ M).insertIdx L.length x = L ++ x :: M := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.cons_append, List.length_cons, List.insertIdx_succ_cons, ih]

theorem erase_lemma (L M : List Bool) (x : Bool) : (L ++ x :: M).eraseIdx L.length = L ++ M := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.cons_append, List.length_cons, List.eraseIdx_cons_succ, ih]

theorem tk (Q R : List Bool) (x : Bool) : (Q ++ x :: R).take (Q.length + 1) = Q ++ [x] := by
  induction Q with
  | nil => rfl
  | cons a Q ih =>
    simp only [List.cons_append, List.length_cons, List.take_succ_cons, ih]

theorem core (X Y : List Bool) (hc : Conflict X Y) (hl : Y.length = X.length + 1) :
    ∃ Q A B, false ∉ A ∧ false ∉ B ∧ X = Q ++ false :: (A ++ B) ∧
      Y = Q ++ false :: (A ++ false :: B) := by
  obtain ⟨_, hX, _, hbn, htk⟩ := hc
  obtain ⟨Q, U, hU, rfl⟩ := decomp X hX
  rw [lz_eq Q U hU] at htk
  have e : Y = Q ++ false :: Y.drop (Q.length + 1) := by
    calc Y = Y.take (Q.length + 1) ++ Y.drop (Q.length + 1) := (List.take_append_drop _ _).symm
      _ = Q ++ false :: Y.drop (Q.length + 1) := by
          rw [← htk, tk]
          simp
  obtain ⟨V, hV⟩ : ∃ V, V = Y.drop (Q.length + 1) := ⟨_, rfl⟩
  rw [← hV] at e
  subst e
  have hVl : V.length = U.length + 1 := by
    simp only [List.length_append, List.length_cons] at hl
    omega
  have hcU := ct_of_nf U hU
  have hcV : V.count true = U.length := by
    unfold bitNorm at hbn
    rw [List.count_append, List.count_append, ct_false_cons, ct_false_cons, hcU] at hbn
    omega
  have hfV : V.count false = 1 := by
    have := ct_add_cf V
    omega
  have hfmem : false ∈ V := List.count_pos_iff.mp (by omega)
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hfmem
  rw [List.count_append, cf_false_cons] at hfV
  have hA : false ∉ A := List.count_eq_zero.mp (by omega)
  have hB : false ∉ B := List.count_eq_zero.mp (by omega)
  have hAB : false ∉ A ++ B := by
    rw [List.mem_append]
    rintro (h | h)
    · exact hA h
    · exact hB h
  have hUAB : U = A ++ B := eq_of_nf U (A ++ B) hU hAB (by
    simp only [List.length_append, List.length_cons] at hVl ⊢
    omega)
  exact ⟨Q, A, B, hA, hB, by rw [hUAB], rfl⟩

end Aux_SecSampling_lemma_9

open SecSampling Aux_SecSampling_lemma_9 in
theorem solution (I : List Bool) :
    (false ∈ I → ∀ J : List Bool, J.length = I.length + 1 →
      (Conflict I J ↔ ∃ i : ℕ, lastZero I ≤ i ∧ i ≤ I.length ∧ J = I.insertIdx i false)) ∧
    (2 ≤ I.count false → ∀ J : List Bool, J.length + 1 = I.length →
      (Conflict J I ↔ J = I.eraseIdx (lastZero I - 1))) ∧
    (I.count false ≤ 1 → ∀ J : List Bool, J.length + 1 = I.length → ¬ Conflict J I) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hI J hJ
    constructor
    · intro hc
      obtain ⟨Q, A, B, hA, hB, rfl, rfl⟩ := core I J hc hJ
      have hAB : false ∉ A ++ B := by
        rw [List.mem_append]
        rintro (h | h)
        · exact hA h
        · exact hB h
      refine ⟨(Q ++ false :: A).length, ?_, ?_, ?_⟩
      · rw [lz_eq Q (A ++ B) hAB]
        simp only [List.length_append, List.length_cons]
        omega
      · simp only [List.length_append, List.length_cons]
        omega
      · have e1 : Q ++ false :: (A ++ B) = (Q ++ false :: A) ++ B := by simp
        have e2 : Q ++ false :: (A ++ false :: B) = (Q ++ false :: A) ++ false :: B := by simp
        rw [e1, e2, ins_lemma]
    · rintro ⟨i, hi1, hi2, rfl⟩
      obtain ⟨P, T, hT, rfl⟩ := decomp I hI
      have hlz := lz_eq P T hT
      rw [hlz] at hi1
      have hins : (P ++ false :: T).insertIdx i false =
          (P ++ false :: T).take i ++ false :: (P ++ false :: T).drop i := by
        have h := ins_lemma ((P ++ false :: T).take i) ((P ++ false :: T).drop i) false
        rw [List.take_append_drop, List.length_take, min_eq_left hi2] at h
        exact h
      rw [hins]
      unfold Conflict
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_take, List.length_drop]
        simp only [List.length_append, List.length_cons] at hi2
        omega
      · simp
      · simp
      · have e : List.count true (P ++ false :: T) =
            List.count true ((P ++ false :: T).take i) +
              List.count true ((P ++ false :: T).drop i) := by
          rw [← List.count_append, List.take_append_drop]
        unfold bitNorm
        rw [e, List.count_append, ct_false_cons]
      · rw [hlz]
        have hle : P.length + 1 ≤ ((P ++ false :: T).take i).length := by
          rw [List.length_take]
          omega
        rw [List.take_append_of_le_length hle, List.take_take, min_eq_left hi1]
  · intro h2 J hJ
    constructor
    · intro hc
      obtain ⟨Q, A, B, hA, hB, rfl, rfl⟩ := core J I hc (by omega)
      have e2 : Q ++ false :: (A ++ false :: B) = (Q ++ false :: A) ++ false :: B := by simp
      rw [e2, lz_eq _ B hB, Nat.add_sub_cancel, erase_lemma]
      simp
    · intro hJeq
      subst hJeq
      have hmem : false ∈ I := List.count_pos_iff.mp (by omega)
      obtain ⟨P, T, hT, rfl⟩ := decomp I hmem
      rw [lz_eq P T hT, Nat.add_sub_cancel, erase_lemma]
      have hcnt : (P ++ false :: T).count false = P.count false + 1 := by
        rw [List.count_append, cf_false_cons, List.count_eq_zero.mpr hT, Nat.zero_add]
      have hP : false ∈ P := List.count_pos_iff.mp (by omega)
      obtain ⟨P', T', hT', rfl⟩ := decomp P hP
      have hTT : false ∉ T' ++ T := by
        rw [List.mem_append]
        rintro (h | h)
        · exact hT' h
        · exact hT h
      have e1 : P' ++ false :: T' ++ T = P' ++ false :: (T' ++ T) := by simp
      have e3 : P' ++ false :: T' ++ false :: T = P' ++ false :: (T' ++ false :: T) := by simp
      rw [e1, e3]
      unfold Conflict
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons]
        omega
      · simp
      · simp
      · unfold bitNorm
        simp only [List.count_append, ct_false_cons]
      · rw [lz_eq P' (T' ++ T) hTT, tk, tk]
  · intro h1 J hJ hc
    obtain ⟨Q, A, B, hA, hB, rfl, rfl⟩ := core J I hc (by omega)
    rw [List.count_append, cf_false_cons, List.count_append, cf_false_cons] at h1
    omega
