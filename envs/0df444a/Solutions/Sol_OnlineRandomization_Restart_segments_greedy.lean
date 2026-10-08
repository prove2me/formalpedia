-- Prove2me | solution 1 for OnlineRandomization.Restart.segments_greedy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T05:08:47.758046+00:00
-- url     : https://prove2.me/submissions/c1315e20-b5b1-4e1f-94fe-246277982914

import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model
import Definitions.Def_OnlineRandomization_Restart_RestartAlgorithm

set_option autoImplicit false

open OnlineRandomization.Restart in
theorem SG9dc_inRH_prefix {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    {p q : List R} (hpq : p <+: q) (hq : InRH F H q) : InRH F H p := by
  intro r' hr' hne
  refine hq r' (hr'.trans hpq) ?_
  rintro rfl
  apply hne
  exact (hpq.eq_of_length (le_antisymm hpq.length_le hr'.length_le)).symm

open OnlineRandomization.Restart in
theorem SG9dc_inRH_single {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (hf0 : F.cost [] [] ≤ H) (x : R) : InRH F H [x] := by
  intro r' hr' hne
  have h0 : r' = [] := by
    rcases List.prefix_cons_iff.mp hr' with h | ⟨l, h1, h2⟩
    · exact h
    · exact absurd (by subst h1; rw [List.prefix_nil.mp h2]) hne
  subst h0
  unfold Game.opt
  refine (Finset.inf'_le _ (Finset.mem_univ (fun i => absurd i.2 (by simp)))).trans ?_
  simpa using hf0

open OnlineRandomization.Restart in
theorem SG9dc_fold_acc {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (l : List R) : ∀ (c : List (List R)) (cur : List R),
    l.foldl (restartStep F H) (c, cur) =
      (c ++ (l.foldl (restartStep F H) ([], cur)).1, (l.foldl (restartStep F H) ([], cur)).2) := by
  induction l with
  | nil => intro c cur; simp
  | cons x l ih =>
    intro c cur
    simp only [List.foldl_cons, restartStep]
    split_ifs with h
    · rw [ih (c ++ [cur]) [x], ih ([] ++ [cur]) [x]]
      try simp
    · rw [ih c (cur ++ [x]), ih [] (cur ++ [x])]
      try simp

open OnlineRandomization.Restart in
theorem SG9dc_state_inRH {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (s : List R) (hs : InRH F H s) : restartState F H s = ([], s) := by
  induction s using List.reverseRecOn with
  | nil => simp [restartState]
  | append_singleton s x ih =>
    have hs' : InRH F H s := SG9dc_inRH_prefix F H (List.prefix_append s [x]) hs
    unfold restartState at ih ⊢
    rw [List.foldl_append, ih hs']
    simp only [List.foldl_cons, List.foldl_nil, restartStep]
    rw [if_neg (by rintro ⟨_, h⟩; exact h hs)]
    try simp

open OnlineRandomization.Restart in
theorem SG9dc_split {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (s t : List R) (hne : s ≠ []) (hs : restartState F H s = ([], s))
    (hnot : ∀ x t', t = x :: t' → ¬ InRH F H (s ++ [x])) :
    segments F H (s ++ t) = s :: segments F H t := by
  cases t with
  | nil =>
    have e : segments F H ([] : List R) = [] := by simp [segments, restartState]
    rw [List.append_nil, e]
    unfold segments
    rw [hs]
    simp [hne]
  | cons x t' =>
    have hstep : restartStep F H ([], s) x = ([s], [x]) := by
      unfold restartStep
      rw [if_pos ⟨hne, hnot x t' rfl⟩]
      try simp
    have e1 : restartState F H (s ++ x :: t') = t'.foldl (restartStep F H) ([s], [x]) := by
      unfold restartState at hs ⊢
      rw [List.foldl_append, hs, List.foldl_cons, hstep]
    have e2 : restartState F H (x :: t') = t'.foldl (restartStep F H) ([], [x]) := by
      unfold restartState
      rw [List.foldl_cons]
      simp [restartStep]
    have hrt : restartState F H (s ++ x :: t') =
        (s :: (restartState F H (x :: t')).1, (restartState F H (x :: t')).2) := by
      rw [e1, e2, SG9dc_fold_acc F H t' [s] [x]]
      rfl
    unfold segments
    rw [hrt]
    split_ifs <;> simp

open OnlineRandomization.Restart in
theorem solution {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (hf0 : F.cost [] [] ≤ H) (r : List R) (hr : r ≠ []) :
    ∃ s : List R, segments F H r = s :: segments F H (r.drop s.length) ∧
      s ≠ [] ∧ s <+: r ∧ InRH F H s ∧
      ∀ p : List R, p <+: r → InRH F H p → p.length ≤ s.length := by
  classical
  set K := Nat.findGreatest (fun k => InRH F H (r.take k)) r.length with hK
  have hlen : 1 ≤ r.length := by
    cases r with
    | nil => exact absurd rfl hr
    | cons _ _ => simp
  have h1 : InRH F H (r.take 1) := by
    cases r with
    | nil => exact absurd rfl hr
    | cons x _ => simpa using SG9dc_inRH_single F H hf0 x
  have hK1 : 1 ≤ K := Nat.le_findGreatest (P := fun k => InRH F H (r.take k)) hlen h1
  have hKle : K ≤ r.length := Nat.findGreatest_le _
  have hPK : InRH F H (r.take K) := Nat.findGreatest_spec (P := fun k => InRH F H (r.take k)) hlen h1
  have hslen : (r.take K).length = K := by simp [hKle]
  have hne : r.take K ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [hslen, List.length_nil] at this
    omega
  have hstate : restartState F H (r.take K) = ([], r.take K) := SG9dc_state_inRH F H _ hPK
  refine ⟨r.take K, ?_, hne, List.take_prefix _ _, hPK, ?_⟩
  · rw [hslen]
    have hnot : ∀ x t', r.drop K = x :: t' → ¬ InRH F H (r.take K ++ [x]) := by
      intro x t' ht hin
      have hKlt : K + 1 ≤ r.length := by
        have := congrArg List.length (List.take_append_drop K r)
        rw [ht, List.length_append, hslen, List.length_cons] at this
        omega
      have hgt := Nat.findGreatest_is_greatest (P := fun k => InRH F H (r.take k))
        (Nat.lt_succ_self K) hKlt
      have hx : r[K]? = some x := by
        rw [← List.head?_drop, ht]
        rfl
      have e : r.take (K + 1) = r.take K ++ [x] := by
        rw [List.take_add_one, hx]
        rfl
      refine hgt ?_
      show InRH F H (r.take (K + 1))
      rw [e]
      exact hin
    have := SG9dc_split F H (r.take K) (r.drop K) hne hstate hnot
    rwa [List.take_append_drop] at this
  · intro p hp hin
    have hpl : p.length ≤ r.length := hp.length_le
    have hpt : r.take p.length = p := by
      obtain ⟨u, rfl⟩ := hp
      simp
    have : InRH F H (r.take p.length) := by rw [hpt]; exact hin
    rw [hslen]
    exact Nat.le_findGreatest (P := fun k => InRH F H (r.take k)) hpl this
