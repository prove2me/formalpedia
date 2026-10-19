-- Prove2me | solution 1 for actuarial_c_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:03:55.12797+00:00
-- url     : https://prove2.me/submissions/957e8a2d-dab1-4df8-adc9-9182987ca338

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_surv

open ActuarialAssurances



lemma actH_filt (h n : ℕ) (hn : n ≤ h+1) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.range (h+1), (if k < n then g k else 0) = ∑ k ∈ Finset.range n, g k := by
  rw [← Finset.sum_filter]; congr 1; ext k; simp; omega

lemma actH_part (h n : ℕ) (p : ℕ → ℝ) (hn : n ≤ h) :
    (∑ j ∈ Finset.range n, p j) + surv h p n = total h p := by
  unfold surv total alive
  rw [← actH_filt h n (by omega), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  split_ifs with h1 h2 <;> first | (exfalso; omega) | ring

theorem solution (h n : ℕ) (p : ℕ → ℝ) (hn : n ≤ h) : (∑ j ∈ Finset.range n, p j)+surv h p n=total h p := by
  exact actH_part h n p hn

