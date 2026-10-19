-- Prove2me | solution 1 for actuarial_c_endowment_annuity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:01:11.478592+00:00
-- url     : https://prove2.me/submissions/e1439dc4-a147-4c24-b1c9-f725e1d162a1

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_endowPath
import Definitions.Def_actuarial_c_endow
import Definitions.Def_actuarial_c_due

open ActuarialAssurances



lemma actH_tp (h n : ℕ) (v : ℝ) (b : ℕ → ℝ) (k : ℕ) :
    termPath h n v b k = if k < n ∧ k < h then v^(k+1)*b k else 0 := by
  unfold termPath death
  rw [Finset.sum_congr rfl (g := fun j => if k = j then (if j < h then v^(j+1)*b j else 0) else 0)
    (by intro j _; split_ifs <;> simp_all)]
  rw [Finset.sum_ite_eq]; simp only [Finset.mem_range]; split_ifs <;> simp_all

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

theorem solution (h n : ℕ) (v : ℝ) (p : ℕ → ℝ) (hn : n ≤ h) (hm : total h p=1) : endow h n v (fun _ => 1) p+(1-v)*due h n v p=1 := by
  rw [actH_dueK]; unfold endow endowPath purePath
  unfold total at hm; refine Eq.trans ?_ hm
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k hk
  have hk' := Finset.mem_range.mp hk
  have e := actH_ann k n v
  rw [actH_tp]
  unfold alive at e ⊢
  by_cases h1 : k < n
  · rw [show min (k+1) n = k+1 by omega] at e
    simp only [if_pos (show k < n ∧ k < h from ⟨h1, by omega⟩), show ¬ (n ≤ k) by omega, if_false]
    linear_combination p k * e
  · rw [show min (k+1) n = n by omega] at e
    simp only [if_neg (show ¬ (k < n ∧ k < h) from fun h' => h1 h'.1), show n ≤ k by omega, if_true]
    linear_combination p k * e

