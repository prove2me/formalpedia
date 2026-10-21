-- Prove2me | solution 1 for YuanDGD.Linear.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:19:25.052429+00:00
-- url     : https://prove2.me/submissions/b3822abb-f964-49bc-bf3b-0a956f39ffe5

import Mathlib
import Definitions.Def_YuanDGD_Linear_Setting

set_option autoImplicit false
open YuanDGD.Linear

theorem solution {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → E p → ℝ)
    (hds : W ∈ doublyStochastic ℝ (Fin n)) (α : ℝ) :
    ∀ k : ℕ, xbar (dgd W f α) (k + 1) = xbar (dgd W f α) k - α • gk f (dgd W f α) k := by
  intro k
  have hcol : ∀ j, ∑ i, W i j = 1 := fun j => sum_col_of_mem_doublyStochastic hds j
  unfold xbar gk
  rw [dgd]
  simp only [mix, PiLp.sub_apply, PiLp.smul_apply, Finset.sum_sub_distrib, ← Finset.smul_sum]
  have hmix : ∑ i, ∑ x, W i x • (dgd W f α k).ofLp x = ∑ x, (dgd W f α k).ofLp x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.sum_smul, hcol x, one_smul]
  rw [hmix, smul_sub, smul_comm α]
