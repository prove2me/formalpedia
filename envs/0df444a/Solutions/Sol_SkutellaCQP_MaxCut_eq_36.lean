-- Prove2me | solution 1 for SkutellaCQP.MaxCut.eq_36
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:22:46.639392+00:00
-- url     : https://prove2.me/submissions/fa6c5f5c-54a6-4398-8913-d41e19e98766

import Mathlib
import Definitions.Def_SkutellaCQP_MaxCut_Setting

open SkutellaCQP.MaxCut Finset

theorem solution {m n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j) (hm : 0 < m) :
    ∀ σ : Fin n → Fin m, cE p w = val p w σ - ∑ j, w j * p j + cut p w σ := by
  classical
  intro σ
  have h : SkutellaCQP.MaxCut.val p w σ + cut p w σ = (∑ j, w j * p j) + cE p w := by
    unfold SkutellaCQP.MaxCut.val SkutellaCQP.MaxCut.compl cut cE
    simp only [mul_add, mul_sum, sum_add_distrib, sum_filter]
    rw [add_assoc]
    congr 1
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    unfold edgeW
    by_cases h : prec p w k j <;> by_cases hs : σ j = σ k <;> simp [h, hs, eq_comm]
  linarith

#print axioms solution
