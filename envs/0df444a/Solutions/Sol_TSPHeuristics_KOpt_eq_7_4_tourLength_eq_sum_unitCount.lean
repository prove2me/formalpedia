-- Prove2me | solution 1 for TSPHeuristics.KOpt.eq_7_4_tourLength_eq_sum_unitCount
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:34:39.086186+00:00
-- url     : https://prove2.me/submissions/33a403ee-91f3-48e1-9b70-2a3e6bb3c990

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_KOpt_CircleInstance
import Definitions.Def_TSPHeuristics_KOpt_UnitEdgeCount

namespace TSPHeuristics.KOpt

lemma aux_ko74_nat (n a b : ℕ) (hab : a ≤ b) (hb : b < n) :
    ((Finset.range n).filter (fun i => if 2 * (b - a) ≤ n then a ≤ i ∧ i < b
      else i < a ∨ b ≤ i)).card = min ((a + n - b) % n) ((b + n - a) % n) := by
  rcases Nat.eq_or_lt_of_le hab with h | h
  · subst h
    have h1 : (Finset.range n).filter (fun i => if 2 * (a - a) ≤ n then a ≤ i ∧ i < a
        else i < a ∨ a ≤ i) = ∅ := by
      ext i; simp
    rw [h1]
    simp
  · have e1 : (b + n - a) % n = b - a := by
      have : b + n - a = (b - a) + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have e2 : (a + n - b) % n = n - (b - a) := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [e1, e2]
    by_cases hc : 2 * (b - a) ≤ n
    · have h1 : (Finset.range n).filter (fun i => if 2 * (b - a) ≤ n then a ≤ i ∧ i < b
          else i < a ∨ b ≤ i) = Finset.Ico a b := by
        ext i; simp only [Finset.mem_filter, Finset.mem_range, if_pos hc, Finset.mem_Ico]
        omega
      rw [h1, Nat.card_Ico]
      omega
    · have h1 : (Finset.range n).filter (fun i => if 2 * (b - a) ≤ n then a ≤ i ∧ i < b
          else i < a ∨ b ≤ i) = Finset.range n \ Finset.Ico a b := by
        ext i; simp only [Finset.mem_filter, Finset.mem_range, if_neg hc, Finset.mem_Ico,
          Finset.mem_sdiff]
        omega
      have hsub : Finset.Ico a b ⊆ Finset.range n := by
        intro i hi; simp only [Finset.mem_Ico] at hi; simp only [Finset.mem_range]; omega
      rw [h1, Finset.card_sdiff_of_subset hsub, Nat.card_Ico, Finset.card_range]
      omega

lemma aux_ko74_card (n : ℕ) (x y : Fin n) :
    (Finset.univ.filter (fun e : Fin n => arcCovers n x y e)).card
      = min ((x.val + n - y.val) % n) ((y.val + n - x.val) % n) := by
  have key : (Finset.univ.filter (fun e : Fin n => arcCovers n x y e)).card =
      ((Finset.range n).filter (fun i =>
        if 2 * (max x.val y.val - min x.val y.val) ≤ n then
          min x.val y.val ≤ i ∧ i < max x.val y.val
        else i < min x.val y.val ∨ max x.val y.val ≤ i)).card := by
    rw [Finset.card_filter, Finset.card_filter]
    unfold arcCovers
    exact Fin.sum_univ_eq_sum_range (fun i => if (if 2 * (max x.val y.val - min x.val y.val) ≤ n then
          min x.val y.val ≤ i ∧ i < max x.val y.val
        else i < min x.val y.val ∨ max x.val y.val ≤ i) then 1 else 0) n
  rw [key]
  rcases le_total x.val y.val with h | h
  · rw [max_eq_right h, min_eq_left h]
    exact aux_ko74_nat n x.val y.val h y.isLt
  · rw [max_eq_left h, min_eq_right h, min_comm]
    exact aux_ko74_nat n y.val x.val h x.isLt

end TSPHeuristics.KOpt

open TSPHeuristics.KOpt

theorem solution (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    TSPHeuristics.Shared.tourLength (cycDist n) τ = ∑ e : Fin n, (unitCount τ e : ℝ) := by
  unfold TSPHeuristics.Shared.tourLength unitCount
  simp only [Finset.card_filter]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_boole]
  unfold cycDist
  rw [aux_ko74_card]
