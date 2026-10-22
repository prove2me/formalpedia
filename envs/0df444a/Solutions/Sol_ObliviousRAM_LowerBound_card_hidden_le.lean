-- Prove2me | solution 1 for ObliviousRAM.LowerBound.card_hidden_le
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T16:46:02.478416+00:00
-- url     : https://prove2.me/submissions/f635fd81-7114-42f6-8d79-1ac4baafb6ea

import Mathlib
import Definitions.Def_ObliviousRAM_LowerBound_Game

open ObliviousRAM.LowerBound
open Classical

noncomputable def oram_run {m : ℕ} (b : ℕ) (s : Option (State m)) (l : List (Action m)) :
    Option (State m) :=
  l.foldl (fun os act => os.bind (fun s => step b s act)) s

theorem oram_run_none {m : ℕ} (b : ℕ) (l : List (Action m)) : oram_run b none l = none := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa [oram_run, List.foldl_cons] using ih

theorem oram_run_cons {m : ℕ} (b : ℕ) (s : State m) (a : Action m) (l : List (Action m)) :
    oram_run b (some s) (a :: l) = oram_run b (step b s a) l := by
  simp [oram_run, List.foldl_cons]

theorem oram_step_hand {m : ℕ} (b : ℕ) (s s' : State m) (a : Action m)
    (h : step b s a = some s') (hs : s.hand.card ≤ b) : s'.hand.card ≤ b := by
  obtain ⟨v, h0⟩ := a
  cases h0 with
  | take =>
    simp only [step] at h
    split at h
    · simp at h
    · split_ifs at h with hc
      simp only [Option.some.injEq] at h
      subst h
      exact (Finset.card_insert_le _ _).trans (by omega)
  | place β =>
    simp only [step] at h
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    exact (Finset.card_erase_le).trans hs
  | nothing =>
    simp only [step, Option.some.injEq] at h
    subst h; exact hs

theorem oram_heads {m : ℕ} (b : ℕ) (s : State m) (v : Fin m) (hs : s.hand.card ≤ b) :
    (Finset.univ.filter fun h : Hidden m => (step b s (v, h)).isSome).card ≤ b + 2 := by
  have hsub : (Finset.univ.filter fun h : Hidden m => (step b s (v, h)).isSome) ⊆
      insert Hidden.take (insert Hidden.nothing (s.hand.image Hidden.place)) := by
    intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
    cases h with
    | take => simp
    | nothing => simp
    | place β =>
      simp only [step] at hh
      split_ifs at hh with hc
      · simp [hc.2]
      · simp at hh
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_insert_le _ _).trans ?_
  have := Finset.card_insert_le Hidden.nothing (s.hand.image Hidden.place)
  have := Finset.card_image_le (s := s.hand) (f := Hidden.place)
  omega

theorem oram_main {m : ℕ} (b : ℕ) (V : List (Fin m)) :
    ∀ s : State m, s.hand.card ≤ b →
      (Finset.univ.filter fun H : Fin V.length → Hidden m =>
        (oram_run b (some s) (List.ofFn fun i => (V.get i, H i))).isSome).card ≤ (b + 2) ^ V.length := by
  induction V with
  | nil =>
    intro s _
    simp only [List.length_nil, pow_zero]
    refine (Finset.card_filter_le _ _).trans ?_
    simp
  | cons v V ih =>
    intro s hs
    set n := V.length
    let P : (Fin (n + 1) → Hidden m) → Prop := fun H =>
      (oram_run b (some s) (List.ofFn fun i => ((v :: V).get i, H i))).isSome
    have key : ∀ H : Fin (n + 1) → Hidden m, P H ↔
        (oram_run b (step b s (v, H 0)) (List.ofFn fun i : Fin n => (V.get i, H i.succ))).isSome := by
      intro H
      simp only [P, List.ofFn_succ, oram_run_cons]
      rfl
    show (Finset.univ.filter P).card ≤ (b + 2) ^ (n + 1)
    rw [Finset.card_eq_sum_card_fiberwise (f := fun H => H 0) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    -- bound each fiber
    have hfib : ∀ h : Hidden m, ((Finset.univ.filter P).filter (fun H => H 0 = h)).card ≤
        if (step b s (v, h)).isSome then (b + 2) ^ n else 0 := by
      intro h
      rcases hst : step b s (v, h) with _ | s'
      · simp only [Option.isSome_none, Bool.false_eq_true, if_false, Nat.le_zero,
          Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro H hH h0
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH
        rw [key, h0, hst, oram_run_none] at hH
        simp at hH
      · simp only [Option.isSome_some, if_true]
        have hs' := oram_step_hand b s s' _ hst hs
        refine le_trans ?_ (ih s' hs')
        apply Finset.card_le_card_of_injOn (fun H => fun i : Fin n => H i.succ)
        · intro H hH
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.mem_setOf_eq] at hH ⊢
          have := (key H).1 hH.1
          rw [hH.2, hst] at this
          exact this
        · intro H1 hH1 H2 hH2 heq
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.mem_setOf_eq] at hH1 hH2
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · rw [hH1.2, hH2.2]
          · exact congrFun heq j
    calc ∑ h : Hidden m, ((Finset.univ.filter P).filter (fun H => H 0 = h)).card
        ≤ ∑ h : Hidden m, (if (step b s (v, h)).isSome then (b + 2) ^ n else 0) :=
          Finset.sum_le_sum (fun h _ => hfib h)
      _ = (Finset.univ.filter fun h : Hidden m => (step b s (v, h)).isSome).card * (b + 2) ^ n := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
      _ ≤ (b + 2) * (b + 2) ^ n := Nat.mul_le_mul_right _ (oram_heads b s v hs)
      _ = (b + 2) ^ (n + 1) := by ring

theorem solution {b m : ℕ} (V : List (Fin m)) :
    (Finset.univ.filter fun H : Fin V.length → Hidden m =>
      Legal b (List.ofFn fun i => (V.get i, H i))).card ≤ (b + 2) ^ V.length := by
  have h := oram_main b V (initState m) (by simp [initState])
  convert h using 3 with H
  simp only [Legal, stateAfter, List.length_ofFn, oram_run]
  rw [List.take_of_length_le (by simp)]
