-- Prove2me | solution 1 for actuarial_c_term_mass
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:05:21.943972+00:00
-- url     : https://prove2.me/submissions/1fe8cc69-fab1-465d-9e42-827862c180fd

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term

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

theorem solution (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hn : n ≤ h) : term h n v b p=∑ j ∈ Finset.range n, v^(j+1)*b j*p j := by
  exact actH_tm h n v b p hn

