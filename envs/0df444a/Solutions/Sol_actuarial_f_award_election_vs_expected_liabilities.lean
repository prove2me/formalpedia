-- Prove2me | solution 1 for actuarial_f_award_election_vs_expected_liabilities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:36:07.797622+00:00
-- url     : https://prove2.me/submissions/16c02334-0be7-46c6-9fc5-7f4316abdd4b

import Mathlib


import Definitions.Def_actuarial_f_firstAwardPV
import Definitions.Def_actuarial_f_firstOptionPV

open ActuarialUnderpinsF

theorem OPV {n h r : ℕ} {p : ℕ → ℕ → ℕ → ℝ} {disc a b growth : ℕ → ℝ}
    (hp : ∀ z ∈ Finset.range n, ∀ i ∈ Finset.range (h+1),
      ∀ j ∈ Finset.range (h+1), 0 ≤ p z i j)
    (hd : ∀ t ∈ Finset.range (h+1), 0 ≤ disc t)
    (hg : ∀ t ∈ Finset.range (h+1), 0 ≤ growth t) (c : ℕ → ℝ) (hc : ∀ z, c z ≤ awardBase a b z) :
    firstOptionPV n h r p disc c growth ≤ firstOptionPV n h r p disc (fun z => awardBase a b z) growth := by
  unfold firstOptionPV expect ActuarialJointD.expect
  refine Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left ?_ (hd t ht)) (hp z hz i hi j hj)
  have hm : 0 ≤ memberDue r i t := by unfold memberDue ActuarialJointD.alive; split_ifs <;> norm_num
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hc z) (hg t ht)) hm

theorem solution (n h r : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ) (disc a b growth : ℕ → ℝ)
    (hp : ∀ z ∈ Finset.range n, ∀ i ∈ Finset.range (h+1),
      ∀ j ∈ Finset.range (h+1), 0 ≤ p z i j)
    (hd : ∀ t ∈ Finset.range (h+1), 0 ≤ disc t)
    (hg : ∀ t ∈ Finset.range (h+1), 0 ≤ growth t) :
    max (firstOptionPV n h r p disc a growth)
        (firstOptionPV n h r p disc b growth) ≤
      firstAwardPV n h r p disc a b growth :=
  by
  unfold firstAwardPV
  exact max_le (OPV hp hd hg a (fun z => le_max_left _ _)) (OPV hp hd hg b (fun z => le_max_right _ _))
