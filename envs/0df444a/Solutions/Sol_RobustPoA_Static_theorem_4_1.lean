-- Prove2me | solution 1 for RobustPoA.Static.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:47:59.314932+00:00
-- url     : https://prove2.me/submissions/2dda5cd4-c6fc-4cd1-a008-2edc2499e9c5

import Mathlib
import Definitions.Def_RobustPoA_Static_Game
import Definitions.Def_RobustPoA_Static_Smoothness
import Definitions.Def_RobustPoA_Static_Distribution

open RobustPoA.Static

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (lam mu ε : ℝ)
    (hsmooth : IsSmooth C lam mu) (hε : 0 ≤ ε) (hεmu : mu * (1 + ε) < 1)
    (σ : (∀ i, S i) →₀ ℝ) (hσ : IsEpsCCE C ε σ) (sstar : ∀ i, S i) :
    expect σ (cost C) ≤ (1 + ε) * lam / (1 - mu * (1 + ε)) * cost C sstar := by
  classical
  have hlinear : expect σ (cost C) = ∑ i, expect σ (C i) := by
    simp only [expect, Finsupp.sum, cost, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hdeviate : expect σ (cost C) ≤
      (1 + ε) * expect σ (fun s => ∑ i, C i (Function.update s i (sstar i))) := by
    rw [hlinear]
    calc
      _ ≤ ∑ i, (1 + ε) * expect σ (fun s => C i (Function.update s i (sstar i))) :=
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
  have hbound := hdeviate.trans (mul_le_mul_of_nonneg_left hsmoothE (by linarith : 0 ≤ 1 + ε))
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : 0 < 1 - mu * (1 + ε))).2
  nlinarith
