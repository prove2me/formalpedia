-- Prove2me | solution 1 for SubmodOrder.query_count
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T05:46:21.685961+00:00
-- url     : https://prove2.me/submissions/723725ed-fb77-4de4-894c-60b0d1a5e2ea

import Mathlib
import Definitions.Def_SubmodOrder_OracleProg
import Definitions.Def_SubmodOrder_thresholdAdd
import Definitions.Def_SubmodOrder_algorithm1

namespace Aux_SubmodOrder_qc

open SubmodOrder

theorem queries_bind {α β γ : Type*} (f : Finset α → ℝ) (p : OracleProg α β)
    (g : β → OracleProg α γ) :
    OracleProg.queries f (OracleProg.bind p g) =
      OracleProg.queries f p + OracleProg.queries f (g (OracleProg.run f p)) := by
  induction p with
  | pure b => simp [OracleProg.bind, OracleProg.queries, OracleProg.run]
  | query S cont ih =>
    simp only [OracleProg.bind, OracleProg.queries, OracleProg.run, ih]
    omega

theorem ta_le {α : Type*} [DecidableEq α] (f : Finset α → ℝ) (k : ℕ) (τ : ℝ) :
    ∀ (l : List α) (S : Finset α) (v : ℝ), OracleProg.queries f (taLoop k τ l S v) ≤ l.length := by
  intro l
  induction l with
  | nil => intro S v; simp [taLoop, OracleProg.queries]
  | cons e es ih =>
    intro S v
    rw [taLoop]
    split_ifs with h
    · rw [OracleProg.queries]
      try dsimp only
      split_ifs with h2
      · have := ih (insert e S) (f (insert e S))
        simp only [List.length_cons]
        omega
      · have := ih S v
        simp only [List.length_cons]
        omega
    · simp [OracleProg.queries]

theorem single_le {α : Type*} (f : Finset α → ℝ) :
    ∀ (l : List α) (m : ℝ), OracleProg.queries f (singletonMaxProg l m) ≤ l.length := by
  intro l
  induction l with
  | nil => intro m; simp [singletonMaxProg, OracleProg.queries]
  | cons e es ih =>
    intro m
    rw [singletonMaxProg, OracleProg.queries]
    have := ih (max m (f {e}))
    simp only [List.length_cons]
    omega

theorem orderList_length {α : Type*} {n : ℕ} (π : α ≃ Fin n) : (orderList π).length = n := by
  simp [orderList]

theorem th_le {α : Type*} [DecidableEq α] {n : ℕ} (π : α ≃ Fin n) (k : ℕ) (f : Finset α → ℝ)
    (τ : ℝ) : OracleProg.queries f (thresholdAdd π k τ) ≤ n := by
  unfold thresholdAdd
  have := ta_le f k τ (orderList π) ∅ 0
  rwa [orderList_length] at this

theorem best_le {α : Type*} [DecidableEq α] {n : ℕ} (π : α ≃ Fin n) (k : ℕ) (f : Finset α → ℝ) :
    ∀ (ts : List ℝ) (best : Finset α × ℝ),
      OracleProg.queries f (bestLoop π k ts best) ≤ ts.length * n := by
  intro ts
  induction ts with
  | nil => intro best; simp [bestLoop, OracleProg.queries]
  | cons t ts ih =>
    intro best
    rw [bestLoop, queries_bind]
    have h1 := th_le π k f t
    have h2 := ih (if best.2 < (OracleProg.run f (thresholdAdd π k t)).2 then
      OracleProg.run f (thresholdAdd π k t) else best)
    calc _ ≤ n + ts.length * n := add_le_add h1 h2
      _ = (t :: ts).length * n := by simp only [List.length_cons]; ring

end Aux_SubmodOrder_qc

open SubmodOrder in
theorem solution {α : Type*} [DecidableEq α] {n : ℕ} (π : α ≃ Fin n) (k : ℕ)
    (f : Finset α → ℝ) :
    (∀ τ : ℝ, OracleProg.queries f (thresholdAdd π k τ) ≤ n) ∧
      ∀ ε : ℝ, OracleProg.queries f (algorithm1 π k ε) ≤ n * (1 + numRounds k ε) := by
  refine ⟨fun τ => Aux_SubmodOrder_qc.th_le π k f τ, fun ε => ?_⟩
  unfold algorithm1
  simp only [Aux_SubmodOrder_qc.queries_bind, OracleProg.queries, add_zero]
  have h1 := Aux_SubmodOrder_qc.single_le f (orderList π) 0
  rw [Aux_SubmodOrder_qc.orderList_length] at h1
  have h2 := Aux_SubmodOrder_qc.th_le π k f
    (OracleProg.run f (singletonMaxProg (orderList π) 0) / k)
  have h3 := Aux_SubmodOrder_qc.best_le π k f
    ((List.range (numRounds k ε - 1)).map fun j =>
      (1 + ε) ^ (j + 1) * (OracleProg.run f (singletonMaxProg (orderList π) 0) / k))
    (OracleProg.run f (thresholdAdd π k (OracleProg.run f (singletonMaxProg (orderList π) 0) / k)))
  rw [List.length_map, List.length_range] at h3
  have hN : 1 ≤ numRounds k ε := le_max_left _ _
  obtain ⟨M, hM⟩ : ∃ M, numRounds k ε = M + 1 := ⟨numRounds k ε - 1, by omega⟩
  rw [hM, Nat.add_sub_cancel] at h3
  rw [hM]
  calc _ ≤ n + (n + M * n) := add_le_add h1 (add_le_add h2 h3)
    _ = n * (1 + (M + 1)) := by ring
