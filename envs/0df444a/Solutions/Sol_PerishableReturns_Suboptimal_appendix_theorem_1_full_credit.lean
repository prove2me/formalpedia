-- Prove2me | solution 1 for PerishableReturns.Suboptimal.appendix_theorem_1_full_credit
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:26:56.521466+00:00
-- url     : https://prove2.me/submissions/e7fd5f83-bc94-46de-bc5d-f6d0af676485

import Mathlib
import Definitions.Def_PerishableReturns_Suboptimal_Model

set_option autoImplicit false
open PerishableReturns.Suboptimal

theorem solution (K : Costs) (c1 : ℝ)
    (hc : K.c < c1) (hp : c1 < K.p) :
    (c1 - K.p - K.g) +
      (K.p + K.g2 - K.c) * (K.p + K.g - c1) / (K.p + K.g2 - K.c3) ≠ 0 := by
  have hg := K.g_nonneg
  have hg1 := K.g1_nonneg
  have h3 := K.c3_lt_c
  have hd : 0 < K.p + K.g2 - K.c3 := by unfold Costs.g2; linarith
  have key : (c1 - K.p - K.g) +
      (K.p + K.g2 - K.c) * (K.p + K.g - c1) / (K.p + K.g2 - K.c3)
      = (K.p + K.g - c1) * (K.c3 - K.c) / (K.p + K.g2 - K.c3) := by
    field_simp
    unfold Costs.g2
    ring
  rw [key]
  exact ne_of_lt (div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (by linarith) (by linarith)) hd)
