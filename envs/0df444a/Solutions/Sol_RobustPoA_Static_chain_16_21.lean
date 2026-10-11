-- Prove2me | solution 1 for RobustPoA.Static.chain_16_21
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:47:01.368342+00:00
-- url     : https://prove2.me/submissions/415c5814-0bc4-405f-92b3-c8a58ce4a0ff

import Mathlib
import Definitions.Def_RobustPoA_Static_Game
import Definitions.Def_RobustPoA_Static_Smoothness
import Definitions.Def_RobustPoA_Static_Distribution

open RobustPoA.Static

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (lam mu : ℝ)
    (hsmooth : IsSmooth C lam mu) (hmu : mu < 1)
    (σ : (∀ i, S i) →₀ ℝ) (hσ : IsCCE C σ) (sstar : ∀ i, S i) :
    expect σ (cost C) ≤ lam / (1 - mu) * cost C sstar := by
  classical
  have hlinear : expect σ (cost C) = ∑ i, expect σ (C i) := by
    simp only [expect, Finsupp.sum, cost, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hdeviate : expect σ (cost C) ≤
      expect σ (fun s => ∑ i, C i (Function.update s i (sstar i))) := by
    rw [hlinear]
    calc
      _ ≤ ∑ i, expect σ (fun s => C i (Function.update s i (sstar i))) :=
        Finset.sum_le_sum fun i _ => hσ.2 i (sstar i)
      _ = _ := by
        simp only [expect, Finsupp.sum, Finset.mul_sum]
        rw [Finset.sum_comm]
  have hsmoothE : expect σ (fun s => ∑ i, C i (Function.update s i (sstar i))) ≤
      lam * cost C sstar + mu * expect σ (cost C) := by
    calc
      _ ≤ expect σ (fun s => lam * cost C sstar + mu * cost C s) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hsmooth s sstar) (hσ.1.1 s)
      _ = _ := by
        have hmass : ∑ s ∈ σ.support, σ s = 1 := hσ.1.2
        simp only [expect, Finsupp.sum, mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, hmass, one_mul]
        congr 1
        simp [Finset.mul_sum, mul_left_comm]
  have hbound := hdeviate.trans hsmoothE
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : 0 < 1 - mu)).2
  nlinarith
