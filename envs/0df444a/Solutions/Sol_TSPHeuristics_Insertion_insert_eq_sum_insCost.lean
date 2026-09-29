-- Prove2me | solution 1 for TSPHeuristics.Insertion.insert_eq_sum_insCost
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:35:21.168032+00:00
-- url     : https://prove2.me/submissions/945e21de-2ed3-439d-ba9d-907f66876b51

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

theorem aux_iesi_step {n : ℕ} (d : Fin n → Fin n → ℝ) (T : List (Fin n)) (k : Fin n)
    (T' : List (Fin n)) (h : IsInsertion d T k T') :
    TSPHeuristics.Shared.cycleLength d T' =
      TSPHeuristics.Shared.cycleLength d T + insCost d T k := by
  obtain ⟨_, pos, hpos, rfl, hmin⟩ := h
  have : insCost d T k = TSPHeuristics.Shared.cycleLength d (T.insertIdx pos k) -
      TSPHeuristics.Shared.cycleLength d T := by
    apply le_antisymm
    · exact Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_le hpos))
    · apply Finset.le_inf'
      intro p hp
      have := hmin p (Nat.lt_succ_iff.1 (Finset.mem_range.1 hp))
      linarith
  rw [this]; ring

end TSPHeuristics.Insertion

open TSPHeuristics.Insertion

theorem solution {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a) :
    TSPHeuristics.Shared.cycleLength d (T n) = ∑ i ∈ Finset.Ico 1 n, insCost d (T i) (a i) := by
  obtain ⟨h1, hstep⟩ := hrun
  have key : ∀ m, 1 ≤ m → m ≤ n →
      TSPHeuristics.Shared.cycleLength d (T m) = ∑ i ∈ Finset.Ico 1 m, insCost d (T i) (a i) := by
    intro m hm hmn
    induction m, hm using Nat.le_induction with
    | base =>
      rw [h1]
      simp [TSPHeuristics.Shared.cycleLength, hd.diag]
    | succ m hm ih =>
      rw [Finset.sum_Ico_succ_top hm, ← ih (by omega),
        aux_iesi_step d (T m) (a m) (T (m + 1)) (hstep m hm (by omega))]
  exact key n hn le_rfl
