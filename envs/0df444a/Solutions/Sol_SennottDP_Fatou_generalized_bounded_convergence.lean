-- Prove2me | solution 1 for SennottDP.Fatou.generalized_bounded_convergence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:42:06.010597+00:00
-- url     : https://prove2.me/submissions/8761e44a-9dcb-42c3-a005-63d9220983be

import Mathlib
import Definitions.Def_SennottDP_Fatou_Basic
import Theorems.Thm_SennottDP_Fatou_generalized_dominated_convergence

open Filter Topology
open scoped ENNReal

open SennottDP.Fatou in
theorem solution {S : Type*} [Countable S] {P : S → ℝ≥0∞}
    {SN : ℕ → Set S} {Q : ℕ → S → ℝ≥0∞} (hA : ApproxDist P SN Q)
    (u : S → ℕ → ℝ) (uL : S → EReal)
    (hu : ∀ j, Tendsto (fun N => (u j N : EReal)) atTop (𝓝 (uL j)))
    (w : ℝ) (hdom : ∀ N, ∀ j ∈ SN N, |u j N| ≤ w) :
    Tendsto (fun N => wsum ((SN N).indicator (Q N)) (fun j => (u j N : EReal))) atTop
      (𝓝 (wsum P uL)) := by
  have hconst : ∀ c : S → ℝ≥0∞, ∑' j, c j = 1 →
      wsum c (fun _ => (w : EReal)) =
        ((ENNReal.ofReal w : ℝ≥0∞) : EReal) - ((ENNReal.ofReal (-w) : ℝ≥0∞) : EReal) := by
    intro c hc
    unfold wsum
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, hc, one_mul, one_mul]
    simp [← EReal.coe_neg]
  have hfin : wsum P (fun _ => (w : EReal)) < ⊤ := by
    rw [hconst P hA.prob, ← EReal.coe_ennreal_toReal ENNReal.ofReal_ne_top,
      ← EReal.coe_ennreal_toReal ENNReal.ofReal_ne_top, ← EReal.coe_sub]
    exact EReal.coe_lt_top _
  refine generalized_dominated_convergence hA u (fun _ _ => w) hdom uL (fun _ => (w : EReal)) hu
    (fun j => tendsto_const_nhds) ?_ hfin
  rw [hconst P hA.prob]
  refine tendsto_const_nhds.congr fun N => ?_
  rw [hconst _ (hA.prob_N N)]


