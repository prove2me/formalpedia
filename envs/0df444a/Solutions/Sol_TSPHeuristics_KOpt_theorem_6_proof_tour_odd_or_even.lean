-- Prove2me | solution 1 for TSPHeuristics.KOpt.theorem_6_proof_tour_odd_or_even
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:51:13.022042+00:00
-- url     : https://prove2.me/submissions/35318048-fb7b-4634-921f-e6a8d7868d31

import Mathlib
import Definitions.Def_TSPHeuristics_KOpt_UnitEdgeCount

namespace TSPHeuristics.KOpt

theorem aux_tpo_ind (n x y e : ℕ) :
    ((if (if 2 * (max x y - min x y) ≤ n then min x y ≤ e ∧ e < max x y
        else e < min x y ∨ max x y ≤ e) then 1 else 0 : ZMod 2))
      = (if 2 * (max x y - min x y) ≤ n then 0 else 1)
        + (if x ≤ e then 1 else 0) + (if y ≤ e then 1 else 0) := by
  by_cases h1 : 2 * (max x y - min x y) ≤ n <;> by_cases h2 : x ≤ e <;>
    by_cases h3 : y ≤ e <;> simp only [h1, h2, h3, if_true, if_false] <;>
    (split_ifs with h4 <;> first | decide | omega)

theorem aux_tpo_cast {n : ℕ} (τ : Equiv.Perm (Fin n)) (e : Fin n) :
    ((unitCount τ e : ℕ) : ZMod 2) =
      ∑ k : Fin n, (if 2 * (max (τ k).val (τ (finRotate n k)).val
        - min (τ k).val (τ (finRotate n k)).val) ≤ n then (0 : ZMod 2) else 1) := by
  unfold unitCount
  rw [Finset.card_filter]
  push_cast
  have h : ∀ k : Fin n,
      (if arcCovers n (τ k) (τ (finRotate n k)) e then (1 : ZMod 2) else 0)
      = (if 2 * (max (τ k).val (τ (finRotate n k)).val
          - min (τ k).val (τ (finRotate n k)).val) ≤ n then 0 else 1)
        + (if (τ k).val ≤ e.val then 1 else 0)
        + (if (τ (finRotate n k)).val ≤ e.val then 1 else 0) := by
    intro k
    unfold arcCovers
    exact aux_tpo_ind n _ _ _
  rw [Finset.sum_congr rfl (fun k _ => h k)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hrot : (∑ k : Fin n, (if (τ (finRotate n k)).val ≤ e.val then (1 : ZMod 2) else 0))
      = ∑ k : Fin n, (if (τ k).val ≤ e.val then (1 : ZMod 2) else 0) :=
    Equiv.sum_comp (finRotate n) (fun k => if (τ k).val ≤ e.val then (1 : ZMod 2) else 0)
  rw [hrot, add_assoc, CharTwo.add_self_eq_zero, add_zero]

end TSPHeuristics.KOpt

open TSPHeuristics.KOpt

theorem solution (n : ℕ) (hn : 3 ≤ n) (τ : Equiv.Perm (Fin n)) :
    (∀ e : Fin n, Even (unitCount τ e)) ∨ (∀ e : Fin n, Odd (unitCount τ e)) := by
  set C : ZMod 2 := ∑ k : Fin n, (if 2 * (max (τ k).val (τ (finRotate n k)).val
        - min (τ k).val (τ (finRotate n k)).val) ≤ n then (0 : ZMod 2) else 1) with hC
  have key : ∀ e : Fin n, ((unitCount τ e : ℕ) : ZMod 2) = C := fun e => aux_tpo_cast τ e
  have hC2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hC2 C with h | h
  · left
    intro e
    rw [← ZMod.natCast_eq_zero_iff_even, key e, h]
  · right
    intro e
    rw [← ZMod.natCast_eq_one_iff_odd, key e, h]
