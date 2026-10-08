-- Prove2me | solution 1 for OnlineRandomization.Simulation.not_winning_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:39:32.957731+00:00
-- url     : https://prove2.me/submissions/d16c01f6-4d70-4ec0-b2db-c488f58ea8bf

import Definitions.Def_OnlineRandomization_Simulation_Winning

open MeasureTheory

namespace OnlineRandomization.Simulation

section Comb
variable {R A : Type*} [Fintype A] [Nonempty A]

lemma sim_ww_mono (F : Game R A) (α : ℝ → ℝ) : ∀ (k k' : ℕ) (r : List R) (a : List A),
    k ≤ k' → WinsWithin F α k r a → WinsWithin F α k' r a
  | 0, 0, r, a, _, h => h
  | 0, k'+1, r, a, _, h => Or.inl h
  | k+1, 0, r, a, hk, _ => absurd hk (by omega)
  | k+1, k'+1, r, a, hk, h => by
      rcases h with h | ⟨x, hx⟩
      · exact Or.inl h
      · exact Or.inr ⟨x, fun y => sim_ww_mono F α k k' _ _ (by omega) (hx y)⟩

lemma sim_playAux_congr (G G' : DetAlg R A) (Q : OfflineAdv R A) : ∀ (m : ℕ) (r : List R) (a : List A),
    (∀ s : List R, r.length < s.length → G s = G' s) → playAux G Q m r a = playAux G' Q m r a
  | 0, r, a, _ => rfl
  | m+1, r, a, h => by
      simp only [playAux]
      cases hq : Q.next a with
      | none => rfl
      | some x =>
        simp only
        rw [h (r ++ [x]) (by simp)]
        exact sim_playAux_congr G G' Q m _ _ (fun s hs => h s (by simp at hs; omega))

lemma sim_win_of_all (F : Game R A) (α : ℝ → ℝ) (Q : OfflineAdv R A) : ∀ (m : ℕ) (r : List R) (a : List A),
    (∀ G : DetAlg R A, α (F.opt (playAux G Q m r a).1) <
      F.cost (playAux G Q m r a).1 (playAux G Q m r a).2) →
    WinsWithin F α m r a
  | 0, r, a, h => by
      have := h (fun _ => Classical.arbitrary A)
      exact this
  | m+1, r, a, h => by
      classical
      cases hq : Q.next a with
      | none =>
        have := h (fun _ => Classical.arbitrary A)
        simp only [playAux, hq] at this
        exact Or.inl this
      | some x =>
        refine Or.inr ⟨x, fun y => sim_win_of_all F α Q m _ _ (fun G' => ?_)⟩
        have := h (Function.update G' (r ++ [x]) y)
        simp only [playAux, hq, Function.update_self] at this
        rwa [sim_playAux_congr (Function.update G' (r ++ [x]) y) G' Q m _ _ (fun s hs => by
          rw [Function.update_of_ne]; rintro rfl; simp at hs)] at this

open Classical in
noncomputable def simPick (F : Game R A) (α : ℝ → ℝ) (N : ℕ) (r : List R) (a : List A) :
    Option R :=
  if α (F.opt r) < F.cost r a then none else
  if h : ∃ x : R, ∀ y : A, WinsWithin F α (N - a.length - 1) (r ++ [x]) (a ++ [y])
  then some h.choose else none

noncomputable def simROfRev (F : Game R A) (α : ℝ → ℝ) (N : ℕ) : List A → List R
  | [] => []
  | _ :: l => match simPick F α N (simROfRev F α N l) l.reverse with
     | none => simROfRev F α N l
     | some x => simROfRev F α N l ++ [x]

noncomputable def simROf (F : Game R A) (α : ℝ → ℝ) (N : ℕ) (a : List A) : List R :=
  simROfRev F α N a.reverse

lemma simROf_snoc (F : Game R A) (α : ℝ → ℝ) (N : ℕ) (a : List A) (y : A) (x : R)
    (h : simPick F α N (simROf F α N a) a = some x) :
    simROf F α N (a ++ [y]) = simROf F α N a ++ [x] := by
  unfold simROf at *
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, simROfRev, List.reverse_reverse]
  rw [h]

noncomputable def simWinQ (F : Game R A) (α : ℝ → ℝ) (N : ℕ) : OfflineAdv R A where
  next := fun a => if a.length < N then simPick F α N (simROf F α N a) a else none
  depth := N
  stop_of_le := by intro a h; simp [not_lt.2 h]

lemma sim_fwd (F : Game R A) (α : ℝ → ℝ) (N : ℕ) (G : DetAlg R A) : ∀ (m : ℕ) (r : List R) (a : List A),
    r = simROf F α N a → a.length + m = N → WinsWithin F α m r a →
    α (F.opt (playAux G (simWinQ F α N) m r a).1) <
      F.cost (playAux G (simWinQ F α N) m r a).1 (playAux G (simWinQ F α N) m r a).2
  | 0, r, a, _, _, h => h
  | m+1, r, a, hr, hl, h => by
      have hn : (simWinQ F α N).next a = simPick F α N r a := by
        simp [simWinQ, hr]; omega
      by_cases himm : α (F.opt r) < F.cost r a
      · have : simPick F α N r a = none := by unfold simPick; simp [himm]
        simp only [playAux, hn, this]; exact himm
      · rcases h with h | hex
        · exact absurd h himm
        · have hm : N - a.length - 1 = m := by omega
          have hex' : ∃ x : R, ∀ y : A, WinsWithin F α (N - a.length - 1) (r ++ [x]) (a ++ [y]) := by
            rw [hm]; exact hex
          have hp : simPick F α N r a = some hex'.choose := by
            unfold simPick; simp [himm, hex']
          obtain ⟨x, hpx, hxs⟩ : ∃ x, simPick F α N r a = some x ∧
              ∀ y, WinsWithin F α m (r ++ [x]) (a ++ [y]) :=
            ⟨hex'.choose, hp, by rw [← hm]; exact hex'.choose_spec⟩
          simp only [playAux, hn, hpx]
          apply sim_fwd F α N G m
          · rw [simROf_snoc F α N a _ x (hr ▸ hpx), hr]
          · simp; omega
          · exact hxs _

theorem initial_position_iff_core {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ) :
    IsWinning F α [] [] ↔
      ∃ Q : OfflineAdv R A, ∀ G : DetAlg R A,
        α (F.opt (play G Q).1) < F.cost (play G Q).1 (play G Q).2 := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨simWinQ F α k, fun G => ?_⟩
    exact sim_fwd F α k G k [] [] (by simp [simROf, simROfRev]) (by simp) hk
  · rintro ⟨Q, hQ⟩
    exact ⟨Q.depth, sim_win_of_all F α Q Q.depth [] [] hQ⟩

end Comb

section NW
variable {R A : Type*} [Fintype A] [Nonempty A]

lemma sim_nw_step (F : Game R A) (α : ℝ → ℝ) (r : List R) (a : List A)
    (h : ¬ IsWinning F α r a) (x : R) : ∃ y : A, ¬ IsWinning F α (r ++ [x]) (a ++ [y]) := by
  classical
  by_contra hc
  push_neg at hc
  choose k hk using hc
  apply h
  refine ⟨Finset.univ.sup k + 1, Or.inr ⟨x, fun y => ?_⟩⟩
  exact sim_ww_mono F α (k y) _ _ _ (Finset.le_sup (Finset.mem_univ y)) (hk y)

open Classical in
noncomputable def simCy (F : Game R A) (α : ℝ → ℝ) (r : List R) (a : List A) (x : R) : A :=
  if h : ∃ y : A, ¬ IsWinning F α (r ++ [x]) (a ++ [y]) then h.choose else Classical.arbitrary A

noncomputable def simAOfRev (F : Game R A) (α : ℝ → ℝ) : List R → List A
  | [] => []
  | x :: l => simAOfRev F α l ++ [simCy F α l.reverse (simAOfRev F α l) x]

noncomputable def simAOf (F : Game R A) (α : ℝ → ℝ) (r : List R) : List A :=
  simAOfRev F α r.reverse

lemma simAOf_snoc (F : Game R A) (α : ℝ → ℝ) (r : List R) (x : R) :
    simAOf F α (r ++ [x]) = simAOf F α r ++ [simCy F α r (simAOf F α r) x] := by
  simp [simAOf, simAOfRev]

noncomputable def simD (F : Game R A) (α : ℝ → ℝ) : DetAlg R A :=
  fun s => (simAOf F α s).getLastD (Classical.arbitrary A)

lemma sim_answers_snoc (G : DetAlg R A) (r : List R) (x : R) :
    G.answers (r ++ [x]) = G.answers r ++ [G (r ++ [x])] := by
  unfold DetAlg.answers
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [List.take_append_of_le_length (by omega)]
  · simp only [List.map_cons, List.map_nil]
    rw [List.take_of_length_le (by simp)]

lemma simD_answers (F : Game R A) (α : ℝ → ℝ) (r : List R) :
    (simD F α).answers r = simAOf F α r := by
  induction r using List.reverseRecOn with
  | nil => simp [DetAlg.answers, simAOf, simAOfRev]
  | append_singleton r x ih =>
    rw [sim_answers_snoc, ih, simAOf_snoc]
    simp [simD, simAOf_snoc]

lemma simAOf_nw (F : Game R A) (α : ℝ → ℝ) (h : ¬ IsWinning F α [] []) (r : List R) :
    ¬ IsWinning F α r (simAOf F α r) := by
  induction r using List.reverseRecOn with
  | nil => simpa [simAOf, simAOfRev] using h
  | append_singleton r x ih =>
    rw [simAOf_snoc]
    have hex := sim_nw_step F α r _ ih x
    unfold simCy
    rw [dif_pos hex]
    exact hex.choose_spec

theorem not_winning_deterministic_core {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ)
    (h : ¬ IsWinning F α [] []) :
    ∃ D : DetAlg R A, IsCompetitive F α D := by
  refine ⟨simD F α, fun r => ?_⟩
  unfold DetAlg.costOn
  rw [simD_answers]
  have := simAOf_nw F α h r
  by_contra hc
  exact this ⟨0, lt_of_not_ge hc⟩

end NW

end OnlineRandomization.Simulation

open OnlineRandomization.Simulation


theorem solution {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ)
    (h : ¬ IsWinning F α [] []) :
    ∃ D : DetAlg R A, IsCompetitive F α D := by
  exact not_winning_deterministic_core F α h
