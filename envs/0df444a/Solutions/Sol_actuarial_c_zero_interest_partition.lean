-- Prove2me | solution 1 for actuarial_c_zero_interest_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:06:06.055804+00:00
-- url     : https://prove2.me/submissions/62399be8-e7f5-48b4-bc27-79793d76f7fb

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term
import Definitions.Def_actuarial_c_pureMass

open ActuarialAssurances



lemma actH_tp (h n : ℕ) (v : ℝ) (b : ℕ → ℝ) (k : ℕ) :
    termPath h n v b k = if k < n ∧ k < h then v^(k+1)*b k else 0 := by
  unfold termPath death
  rw [Finset.sum_congr rfl (g := fun j => if k = j then (if j < h then v^(j+1)*b j else 0) else 0)
    (by intro j _; split_ifs <;> simp_all)]
  rw [Finset.sum_ite_eq]; simp only [Finset.mem_range]; split_ifs <;> simp_all

lemma actH_filt (h n : ℕ) (hn : n ≤ h+1) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.range (h+1), (if k < n then g k else 0) = ∑ k ∈ Finset.range n, g k := by
  rw [← Finset.sum_filter]; congr 1; ext k; simp; omega

lemma actH_tm (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hn : n ≤ h) :
    term h n v b p = ∑ j ∈ Finset.range n, v^(j+1)*b j*p j := by
  unfold term; simp only [actH_tp]
  rw [← actH_filt h n (by omega)]; apply Finset.sum_congr rfl; intro k _
  by_cases h1 : k < n
  · rw [if_pos ⟨h1, by omega⟩, if_pos h1]; ring
  · rw [if_neg (fun h' => h1 h'.1), if_neg h1, mul_zero]

lemma actH_part (h n : ℕ) (p : ℕ → ℝ) (hn : n ≤ h) :
    (∑ j ∈ Finset.range n, p j) + surv h p n = total h p := by
  unfold surv total alive
  rw [← actH_filt h n (by omega), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  split_ifs with h1 h2 <;> first | (exfalso; omega) | ring

theorem solution (h n : ℕ) (p : ℕ → ℝ) (hn : n ≤ h) (hm : total h p=1) : term h n 1 (fun _ => 1) p+pureMass h n 1 p=1 := by
  refine Eq.trans ?_ hm; rw [actH_tm h n 1 _ p hn, ← actH_part h n p hn]; unfold pureMass; simp

