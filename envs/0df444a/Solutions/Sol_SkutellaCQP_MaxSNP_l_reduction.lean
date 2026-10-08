-- Prove2me | solution 1 for SkutellaCQP.MaxSNP.l_reduction
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:17:40.452988+00:00
-- url     : https://prove2.me/submissions/337b5af6-e397-4028-9929-90d7cf8f1e3c

import Theorems.Thm_SkutellaCQP_MaxSNP_lemma_7_1_b
import Theorems.Thm_SkutellaCQP_MaxSNP_l_condition_1
import Theorems.Thm_SkutellaCQP_MaxSNP_l_condition_2

open SkutellaCQP.MaxSNP

theorem solution {n m : ℕ} (I : Occ3Max3Sat n m) (hI : I.IsValid) :
    ∃ S₀ : Sched n m, Feasible I S₀ ∧ VAL S₀ = (4 * n + 4 * m : ℝ) - optSat I ∧
      (∀ S, Feasible I S → VAL S₀ ≤ VAL S) ∧ VAL S₀ ≤ 32 * optSat I ∧
      ∀ S, Feasible I S → (optSat I : ℝ) - satCount I (SAT S) ≤ VAL S - VAL S₀ := by
  obtain ⟨S₀, hS₀, hvalue, hopt⟩ := lemma_7_1_b I hI
  obtain ⟨hbound, hscale⟩ := l_condition_1 I hI S₀ hS₀ hopt
  exact ⟨S₀, hS₀, hvalue, hopt, hbound.trans hscale,
    fun S hS => l_condition_2 I hI S₀ hS₀ hopt S hS⟩

#print axioms solution
