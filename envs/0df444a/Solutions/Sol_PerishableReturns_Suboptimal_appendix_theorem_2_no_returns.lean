-- Prove2me | solution 1 for PerishableReturns.Suboptimal.appendix_theorem_2_no_returns
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:26:58.579974+00:00
-- url     : https://prove2.me/submissions/dee1f773-0ac0-43b5-8427-7bf57a3e36fc

import Mathlib
import Definitions.Def_PerishableReturns_Suboptimal_Model

set_option autoImplicit false
open PerishableReturns.Suboptimal

theorem solution (K : Costs) (c1 : ℝ)
    (hc : K.c < c1) (hp : c1 < K.p) :
    ((0 = (c1 - K.p - K.g) +
      (K.p + K.g2 - K.c) * (K.p + K.g - K.c3) / (K.p + K.g2 - K.c3)) ↔
      c1 = K.c - K.g1 * (K.c - K.c3) / (K.p + K.g2 - K.c3)) ∧
    0 ≠ (c1 - K.p - K.g) +
      (K.p + K.g2 - K.c) * (K.p + K.g - K.c3) / (K.p + K.g2 - K.c3) := by
  have hg := K.g_nonneg
  have hg1 := K.g1_nonneg
  have h3 := K.c3_lt_c
  have hd : 0 < K.p + K.g2 - K.c3 := by unfold Costs.g2; linarith
  have huv : (K.p + K.g2 - K.c) * (K.p + K.g - K.c3) / (K.p + K.g2 - K.c3)
      = K.p + K.g - K.c + K.g1 * (K.c - K.c3) / (K.p + K.g2 - K.c3) := by
    field_simp
    unfold Costs.g2
    ring
  have hv : 0 ≤ K.g1 * (K.c - K.c3) / (K.p + K.g2 - K.c3) :=
    div_nonneg (mul_nonneg hg1 (by linarith)) hd.le
  rw [huv]
  refine ⟨?_, ?_⟩
  · constructor <;> intro h <;> linarith
  · intro h; linarith
