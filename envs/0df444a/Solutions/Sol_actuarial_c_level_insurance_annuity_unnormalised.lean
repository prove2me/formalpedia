-- Prove2me | solution 1 for actuarial_c_level_insurance_annuity_unnormalised
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:02:58.181998+00:00
-- url     : https://prove2.me/submissions/d077400b-d7ae-4e0f-9d77-cb880d5981b4

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_due

open ActuarialAssurances



lemma actH_path (h : ℕ) (v : ℝ) (b : ℕ → ℝ) (k : ℕ) :
    path h v b k = if k < h then v^(k+1)*b k else 0 := by
  unfold path death; simp only [mul_ite, mul_one, mul_zero]; rw [Finset.sum_ite_eq]; simp [Finset.mem_range]

lemma actH_dueK (h n : ℕ) (v : ℝ) (p : ℕ → ℝ) :
    due h n v p = ∑ k ∈ Finset.range (h+1), p k * ∑ j ∈ Finset.range n, v^j * alive k j := by
  unfold due surv
  simp only [Finset.mul_sum]; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; ring

lemma actH_ann (k n : ℕ) (v : ℝ) :
    (1 - v) * ∑ j ∈ Finset.range n, v^j * alive k j = 1 - v ^ (min (k+1) n) := by
  have e : ∑ j ∈ Finset.range n, v^j * alive k j = ∑ j ∈ Finset.range (min (k+1) n), v^j := by
    unfold alive
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n) (fun j => j < min (k+1) n)]
    rw [Finset.sum_eq_zero (s := Finset.filter (fun j => ¬ j < min (k+1) n) (Finset.range n))
      (by intro j hj; simp at hj; rw [if_neg (by omega), mul_zero]), add_zero]
    have : Finset.filter (fun j => j < min (k+1) n) (Finset.range n) = Finset.range (min (k+1) n) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this]; apply Finset.sum_congr rfl; intro j hj; simp at hj; simp [show j ≤ k by omega]
  rw [e]
  have := geom_sum_mul v (min (k+1) n)
  linarith

lemma actH_level (h : ℕ) (v : ℝ) (p : ℕ → ℝ) :
    epv h v (fun _ => 1) p + (1-v)*due h h v p + v^h*surv h p h = total h p := by
  rw [actH_dueK]; unfold epv surv total
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k hk
  have hk' := Finset.mem_range.mp hk
  have e := actH_ann k h v
  rw [actH_path]
  unfold alive at e ⊢
  by_cases h1 : k < h
  · rw [show min (k+1) h = k+1 by omega] at e
    simp only [if_pos h1, show ¬ (h ≤ k) by omega, if_false]
    linear_combination p k * e
  · rw [show min (k+1) h = h by omega] at e
    simp only [if_neg h1, show h ≤ k by omega, if_true]
    linear_combination p k * e

theorem solution (h : ℕ) (v : ℝ) (p : ℕ → ℝ) : epv h v (fun _ => 1) p+(1-v)*due h h v p+v^h*surv h p h=total h p := by
  exact actH_level h v p

