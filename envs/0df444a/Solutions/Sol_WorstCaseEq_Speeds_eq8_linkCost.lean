-- Prove2me | solution 1 for WorstCaseEq.Speeds.eq8_linkCost
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:29:52.272985+00:00
-- url     : https://prove2.me/submissions/958e1a1a-512b-4371-9b09-194d3e6b5c62

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Speeds_Model

open Finset WorstCaseEq.Speeds WorstCaseEq.Identical

private lemma marginal {n m : ℕ} (p : Fin n → Fin m → ℝ)
    (hp : ∀ i, ∑ j, p i j = 1) (k : Fin n) (f : Fin m → ℝ) :
    ∑ a : Fin n → Fin m, AGT.profileProb p a * f (a k) = ∑ j, p k j * f j := by
  classical
  let g : Fin n → Fin m → ℝ := fun i j => p i j * if i = k then f j else 1
  have hg (a : Fin n → Fin m) : (∏ i, g i (a i)) = AGT.profileProb p a * f (a k) := by
    simp only [g, prod_mul_distrib, AGT.profileProb]
    congr 1
    simp
  have hsum := Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset (Fin m))) g
  simp only [Fintype.piFinset_univ] at hsum
  simp_rw [hg] at hsum
  rw [← hsum]
  · rw [prod_eq_single k]
    · simp [g]
    · intro i _ hi
      simp [g, hi, hp i]
    · simp

theorem solution {n m : ℕ} (w : Fin n → ℝ) (s : Fin m → ℝ) (p : Fin n → Fin m → ℝ)
    (hp : AGT.IsMixedProfile p) :
    ∀ i j, -AGT.expectedPayoff (WorstCaseEq.Speeds.payoff w s) (Function.update p i (WorstCaseEq.Identical.pureLottery j)) i
        = WorstCaseEq.Speeds.linkCost w s p i j ∧
      WorstCaseEq.Speeds.linkCost w s p i j = (WorstCaseEq.Identical.expTraffic w p j + (1 - p i j) * w i) / s j := by
  classical
  intro i j
  let q := Function.update p i (pureLottery j)
  have hq : ∀ k, ∑ l, q k l = 1 := by
    intro k
    by_cases h : k = i
    · subst k; simp [q, pureLottery]
    · simp [q, Function.update_of_ne h, (hp k).2]
  have hsupp (a : Fin n → Fin m) (h : a i ≠ j) : AGT.profileProb q a = 0 := by
    apply prod_eq_zero (mem_univ i)
    simp [q, pureLottery, h]
  have hcost : -AGT.expectedPayoff (WorstCaseEq.Speeds.payoff w s) q i =
      (∑ a : Fin n → Fin m, AGT.profileProb q a * load w a j) / s j := by
    simp only [AGT.expectedPayoff, WorstCaseEq.Speeds.payoff, mul_neg]
    rw [Finset.sum_neg_distrib, neg_neg, Finset.sum_div]
    apply sum_congr rfl
    intro a _
    by_cases h : a i = j
    · rw [h, mul_div_assoc]
    · simp [hsupp a h]
  have hl : (∑ a : Fin n → Fin m, AGT.profileProb q a * load w a j) =
      ∑ k, q k j * w k := by
    simp only [load, sum_filter, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    rw [marginal q hq k (fun l => if l = j then w k else 0)]
    simp
  constructor
  · rw [hcost, hl]
    unfold WorstCaseEq.Speeds.linkCost
    congr 1
    rw [← sum_erase_add _ _ (mem_univ i)]
    simp only [q, Function.update_self, pureLottery, if_true, one_mul]
    rw [add_comm]
    congr 1
    apply sum_congr rfl
    intro k hk
    rw [Function.update_of_ne (ne_of_mem_erase hk)]
  · unfold WorstCaseEq.Speeds.linkCost expTraffic
    congr 1
    rw [← sum_erase_add _ _ (mem_univ i)]
    ring

#print axioms solution
