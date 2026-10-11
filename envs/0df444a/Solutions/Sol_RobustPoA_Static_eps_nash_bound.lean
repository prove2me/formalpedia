-- Prove2me | solution 1 for RobustPoA.Static.eps_nash_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:40:56.177761+00:00
-- url     : https://prove2.me/submissions/e4a54996-a562-405f-b30f-79df0ba61215

import Mathlib
import Definitions.Def_RobustPoA_Static_Game
import Definitions.Def_RobustPoA_Static_Smoothness

open RobustPoA.Static

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (lam mu ε : ℝ)
    (hsmooth : IsSmooth C lam mu) (hε : 0 ≤ ε) (hεmu : mu * (1 + ε) < 1)
    (s : ∀ i, S i) (hs : IsEpsNash C ε s)
    (sstar : ∀ i, S i) (hopt : ∀ t : ∀ i, S i, cost C sstar ≤ cost C t) :
    cost C s ≤ (1 + ε) * lam / (1 - mu * (1 + ε)) * cost C sstar := by
  have hsum : cost C s ≤ (1 + ε) * ∑ i, C i (Function.update s i (sstar i)) := by
    simpa only [cost, Finset.mul_sum] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hs i (sstar i))
  have hbound := hsum.trans (mul_le_mul_of_nonneg_left (hsmooth s sstar) (by linarith : 0 ≤ 1 + ε))
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : 0 < 1 - mu * (1 + ε))).2
  nlinarith
