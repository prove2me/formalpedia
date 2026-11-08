-- Prove2me | solution 1 for SecSampling.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:18:26.180199+00:00
-- url     : https://prove2.me/submissions/b658366e-c8d3-4972-b41e-f2b286c5ebee

import Mathlib
import Definitions.Def_SecSampling_ConflictGraph

namespace Aux_SecS13

open SecSampling

theorem idx_rep (t : ℕ) (Z : List Bool) :
    (List.replicate t true ++ false :: Z).idxOf false = t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.replicate_succ, List.cons_append, List.idxOf_cons_ne _ (by decide), ih]

theorem lz_decomp (X : List Bool) (t : ℕ) :
    lastZero (X ++ false :: List.replicate t true) = X.length + 1 := by
  unfold lastZero
  rw [if_pos (by simp)]
  have : (X ++ false :: List.replicate t true).reverse =
      List.replicate t true ++ false :: X.reverse := by
    simp [List.reverse_append, List.reverse_replicate]
  rw [this, idx_rep]
  simp only [List.length_append, List.length_cons, List.length_replicate]
  omega

theorem decomp (I : List Bool) (h : false ∈ I) :
    ∃ (X : List Bool) (t : ℕ), I = X ++ false :: List.replicate t true := by
  have key : ∀ R : List Bool, false ∈ R →
      ∃ (t : ℕ) (Y : List Bool), R = List.replicate t true ++ false :: Y := by
    intro R
    induction R with
    | nil => intro h; simp at h
    | cons b R ih =>
      intro hR
      cases b
      · exact ⟨0, R, rfl⟩
      · have hR' : false ∈ R := by simpa using hR
        obtain ⟨t, Y, rfl⟩ := ih hR'
        exact ⟨t + 1, Y, by simp [List.replicate_succ]⟩
  obtain ⟨t, Y, hY⟩ := key I.reverse (List.mem_reverse.mpr h)
  refine ⟨Y.reverse, t, ?_⟩
  rw [← List.reverse_reverse I, hY]
  simp [List.reverse_append, List.reverse_replicate]

theorem false_mem_of_count (L : List Bool) (h : L.count true < L.length) : false ∈ L := by
  by_contra hf
  have : L.count true = L.length := by
    rw [List.count_eq_length]
    intro b hb
    cases b
    · exact absurd hb hf
    · rfl
  omega

theorem take_take_eq {A B : List Bool} {a b : ℕ} (hab : a ≤ b) (h : A.take b = B.take b) :
    A.take a = B.take a := by
  have h1 : (A.take b).take a = (B.take b).take a := by rw [h]
  rwa [List.take_take, List.take_take, min_eq_left hab] at h1

theorem lz_pos (I : List Bool) (h : false ∈ I) : 1 ≤ lastZero I := by
  obtain ⟨X, t, rfl⟩ := decomp I h
  rw [lz_decomp]; omega

theorem lz_gt (A B : List Bool) (h : Conflict A B) : lastZero A < lastZero B := by
  obtain ⟨hlen, hA, hB, hbn, htake⟩ := h
  obtain ⟨X, t, rfl⟩ := decomp A hA
  rw [lz_decomp] at htake ⊢
  have hta : (X ++ false :: List.replicate t true).take (X.length + 1) = X ++ [false] := by
    rw [List.take_length_add_append]; simp
  rw [hta] at htake
  have hsplit := List.take_append_drop (X.length + 1) B
  have hcount : B.count true = (B.take (X.length + 1)).count true +
      (B.drop (X.length + 1)).count true := by
    conv_lhs => rw [← hsplit]
    rw [List.count_append]
  unfold bitNorm at hbn
  rw [← htake] at hcount
  simp only [List.count_append, List.count_cons, List.count_replicate, List.count_nil] at hbn hcount
  have hlenB : (B.drop (X.length + 1)).length = B.length - (X.length + 1) := List.length_drop
  simp only [List.length_append, List.length_cons, List.length_replicate] at hlen
  have hfd : false ∈ B.drop (X.length + 1) := by
    apply false_mem_of_count
    simp at hbn hcount
    omega
  obtain ⟨Z, u, hZ⟩ := decomp _ hfd
  have hBeq : B = ((X ++ [false]) ++ Z) ++ false :: List.replicate u true := by
    rw [← hsplit, ← htake, hZ]
    simp only [List.append_assoc]
  rw [hBeq, lz_decomp]
  simp

theorem conflict_trans (A B C : List Bool) (h1 : Conflict A B) (h2 : Conflict B C) :
    Conflict A C := by
  have hlt := lz_gt A B h1
  obtain ⟨l1, a1, b1, n1, t1⟩ := h1
  obtain ⟨l2, a2, b2, n2, t2⟩ := h2
  refine ⟨by omega, a1, b2, n1.trans n2, ?_⟩
  rw [t1]
  exact take_take_eq hlt.le t2

theorem desc_conflict (I J : List Bool) (h : IsDescendant I J) : Conflict I J := by
  obtain ⟨P, hP⟩ := h
  induction P generalizing I with
  | nil =>
    simp only [List.nil_append, IsMonotonePath, List.isChain_cons_cons,
      List.isChain_singleton, and_true] at hP
    exact hP.1
  | cons K P ih =>
    simp only [List.cons_append, IsMonotonePath, List.isChain_cons_cons] at hP
    exact conflict_trans I K J hP.1.1 (ih K hP.2)

end Aux_SecS13

open SecSampling Aux_SecS13 in
theorem solution (q : LZStrategy) (hq : IsLZStrategy q) (I J : List Bool)
    (hIJ : IsDescendant I J) :
    winLZ q J ≤ 1 - winLZ q I := by
  have hc := desc_conflict I J hIJ
  have hlt := lz_gt I J hc
  obtain ⟨_, hI, hJ, hbn, htake⟩ := hc
  have ha := lz_pos I hI
  unfold winLZ
  rw [if_pos hI, if_pos hJ, hbn]
  unfold stopProbAt
  set a := lastZero I with ha_def
  set b := lastZero J with hb_def
  set m := bitNorm J
  have hpref : ∀ j, j ≤ a → J.take j = I.take j := by
    intro j hj
    exact (take_take_eq hj htake).symm
  have hq0 : ∀ L, 0 ≤ q m L := fun L => (hq m L).1
  have hq1 : ∀ L, q m L ≤ 1 := fun L => (hq m L).2
  have hsplit : ∏ j ∈ Finset.Ico 1 b, (1 - q m (J.take j)) =
      (∏ j ∈ Finset.Ico 1 a, (1 - q m (I.take j))) * (1 - q m (I.take a)) *
        ∏ j ∈ Finset.Ico (a + 1) b, (1 - q m (J.take j)) := by
    rw [← Finset.prod_Ico_consecutive _ (show 1 ≤ a + 1 by omega) (show a + 1 ≤ b by omega),
      Finset.prod_Ico_succ_top ha, hpref a le_rfl]
    congr 2
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [hpref j (by omega)]
  rw [hsplit]
  set P := ∏ j ∈ Finset.Ico 1 a, (1 - q m (I.take j))
  set R := ∏ j ∈ Finset.Ico (a + 1) b, (1 - q m (J.take j))
  have hP0 : 0 ≤ P := Finset.prod_nonneg (fun j _ => by linarith [hq1 (I.take j)])
  have hP1 : P ≤ 1 := Finset.prod_le_one (fun j _ => by linarith [hq1 (I.take j)])
    (fun j _ => by linarith [hq0 (I.take j)])
  have hR0 : 0 ≤ R := Finset.prod_nonneg (fun j _ => by linarith [hq1 (J.take j)])
  have hR1 : R ≤ 1 := Finset.prod_le_one (fun j _ => by linarith [hq1 (J.take j)])
    (fun j _ => by linarith [hq0 (J.take j)])
  have hqa0 := hq0 (I.take a)
  have hqa1 := hq1 (I.take a)
  have hqb0 := hq0 (J.take b)
  have hqb1 := hq1 (J.take b)
  have hK : 0 ≤ P * (1 - q m (I.take a)) := mul_nonneg hP0 (by linarith)
  have hqR : q m (J.take b) * R ≤ 1 := by nlinarith
  have h1 : q m (J.take b) * (P * (1 - q m (I.take a)) * R) ≤ P * (1 - q m (I.take a)) := by
    have := mul_le_mul_of_nonneg_left hqR hK
    nlinarith
  nlinarith
