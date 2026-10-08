-- Prove2me | solution 1 for OnlineRandomization.Simulation.adversary_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T13:30:36.303299+00:00
-- url     : https://prove2.me/submissions/c96488ba-3a76-4467-82f4-23b091981eb6

import Mathlib
import Definitions.Def_OnlineRandomization_Simulation_Model

set_option autoImplicit false

open OnlineRandomization.Simulation in
theorem c1121132_filterMap_range {R : Type*} (r : List R) :
    ∀ n : ℕ, (List.range n).filterMap (fun j => r[j]?) = r.take n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filterMap_append, ih, List.take_add_one]
    simp only [List.filterMap_cons, List.filterMap_nil]
    cases h : r[n]? <;> simp

open OnlineRandomization.Simulation in
theorem c1121132_inv {R A : Type*} (G : DetAlg R A) (Q : OfflineAdv R A) :
    ∀ (k : ℕ) (r : List R) (a : List A),
      r.length = a.length →
      (∀ j, j < a.length → Q.next (a.take j) = r[j]?) →
      (playAux G Q k r a).1.length = (playAux G Q k r a).2.length ∧
      (∀ j, j < (playAux G Q k r a).2.length →
        Q.next ((playAux G Q k r a).2.take j) = (playAux G Q k r a).1[j]?) := by
  intro k
  induction k with
  | zero =>
    intro r a h1 h2
    exact ⟨h1, h2⟩
  | succ k ih =>
    intro r a h1 h2
    simp only [playAux]
    cases hq : Q.next a with
    | none => exact ⟨h1, h2⟩
    | some x =>
      simp only
      apply ih
      · simp [h1]
      · intro j hj
        simp only [List.length_append, List.length_singleton] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · rw [List.take_append_of_le_length (le_of_lt hj),
            List.getElem?_append_left (by omega)]
          exact h2 j hj
        · subst hj
          rw [List.take_append_of_le_length le_rfl, List.take_length, hq,
            ← h1, List.getElem?_append_right le_rfl]
          simp

open OnlineRandomization.Simulation in
theorem solution {R A : Type*} (Q : OfflineAdv R A)
    (D : DetAlg R A) :
    ∃ S : OnlineAdv R A, S.toOfflineAdv = Q ∧
      ∀ G : DetAlg R A,
        onlineAnswers G S = D.answers (play G Q).1 := by
  refine ⟨⟨Q, fun b => D ((List.range (b.length + 1)).filterMap
      (fun j => Q.next (b.take j)))⟩, rfl, ?_⟩
  intro G
  obtain ⟨hlen, hinv⟩ := c1121132_inv G Q Q.depth [] [] rfl (by simp)
  unfold onlineAnswers DetAlg.answers
  change List.map _ (List.range (play G Q).2.length) =
    List.map _ (List.range (play G Q).1.length)
  unfold play
  rw [hlen]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  simp only
  congr 1
  rw [List.length_take, show min i (playAux G Q Q.depth [] []).2.length = i by omega,
    ← c1121132_filterMap_range (playAux G Q Q.depth [] []).1 (i + 1)]
  apply List.filterMap_congr
  intro j hj
  rw [List.mem_range] at hj
  rw [List.take_take, show min j i = j by omega]
  exact hinv j (by omega)
