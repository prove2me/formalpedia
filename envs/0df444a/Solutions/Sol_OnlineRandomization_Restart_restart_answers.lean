-- Prove2me | solution 1 for OnlineRandomization.Restart.restart_answers
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T06:17:41.786157+00:00
-- url     : https://prove2.me/submissions/81699b2a-548c-4bdb-bb5b-6f80931d6c29

import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model
import Definitions.Def_OnlineRandomization_Restart_RestartAlgorithm

set_option autoImplicit false

open OnlineRandomization.Restart in
theorem ra_answers_snoc {R A : Type*} (G : DetAlg R A) (r : List R) (x : R) :
    G.answers (r ++ [x]) = G.answers r ++ [G (r ++ [x])] := by
  unfold DetAlg.answers
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [List.take_append_of_le_length (by omega)]
  · simp only [List.map_singleton, List.singleton_inj]
    rw [List.take_of_length_le (by simp)]

open OnlineRandomization.Restart in
theorem ra_state_snoc {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (r : List R) (x : R) :
    restartState F H (r ++ [x]) = restartStep F H (restartState F H r) x := by
  unfold restartState
  rw [List.foldl_append]
  rfl

open OnlineRandomization.Restart in
theorem ra_state_flatten {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (r : List R) :
    (restartState F H r).1.flatten ++ (restartState F H r).2 = r := by
  induction r using List.reverseRecOn with
  | nil => rfl
  | append_singleton r x ih =>
    rw [ra_state_snoc]
    unfold restartStep
    split_ifs with h
    · simp only [List.flatten_append, List.flatten_singleton]
      rw [ih]
    · simp only
      rw [← List.append_assoc, ih]

open OnlineRandomization.Restart in
theorem ra_segments_map {R A B : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (f : List R → List B) (hf : f [] = []) (r : List R) :
    ((segments F H r).map f).flatten =
      ((restartState F H r).1.map f).flatten ++ f (restartState F H r).2 := by
  unfold segments
  split_ifs with h
  · rw [h, hf, List.append_nil]
  · simp

open OnlineRandomization.Restart in
theorem ra_restart_answers {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (AH : DetAlg R A) (r : List R) :
    (restart F H AH).answers r =
      ((restartState F H r).1.map AH.answers).flatten ++ AH.answers (restartState F H r).2 := by
  induction r using List.reverseRecOn with
  | nil => rfl
  | append_singleton r x ih =>
    rw [ra_answers_snoc, ih]
    have hc : restart F H AH (r ++ [x]) = AH (restartState F H (r ++ [x])).2 := rfl
    rw [hc, ra_state_snoc]
    unfold restartStep
    split_ifs with h
    · simp only [List.map_append, List.flatten_append, List.map_singleton,
        List.flatten_singleton, List.append_assoc]
      rw [show AH.answers [x] = [AH [x]] from ra_answers_snoc AH [] x]
    · simp only
      rw [ra_answers_snoc, List.append_assoc]

open OnlineRandomization.Restart in
theorem solution {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (AH : DetAlg R A) (r : List R) :
    (segments F H r).flatten = r ∧
      (restart F H AH).answers r = ((segments F H r).map AH.answers).flatten := by
  refine ⟨?_, ?_⟩
  · have := ra_segments_map F H (fun l : List R => l) rfl r
    simp only [List.map_id'] at this
    rw [this, ra_state_flatten]
  · rw [ra_segments_map F H AH.answers rfl r, ra_restart_answers]
