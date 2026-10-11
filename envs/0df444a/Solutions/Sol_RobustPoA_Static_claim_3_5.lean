-- Prove2me | solution 1 for RobustPoA.Static.claim_3_5
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:35:36.989171+00:00
-- url     : https://prove2.me/submissions/5eabedf0-1286-4113-92b0-34a0c15c53cf

import Mathlib
import Definitions.Def_RobustPoA_Static_Game
import Definitions.Def_RobustPoA_Static_Smoothness

open RobustPoA.Static

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (lam mu : ℝ)
    (hsmooth : IsSmooth C lam mu) (hlam : 0 < lam) (hmu : mu < 1)
    (s : ∀ i, S i) (hs : IsPureNash C s)
    (sstar : ∀ i, S i) (hopt : ∀ t : ∀ i, S i, cost C sstar ≤ cost C t) :
    cost C s ≤ lam / (1 - mu) * cost C sstar := by
  have hsum : cost C s ≤ ∑ i, C i (Function.update s i (sstar i)) :=
    Finset.sum_le_sum fun i _ => hs i (sstar i)
  have hbound := hsum.trans (hsmooth s sstar)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : 0 < 1 - mu)).2
  nlinarith
