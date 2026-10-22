-- Prove2me | solution 1 for PerishableReturns.Coordination.theorem_3_credit_range
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:27:02.96391+00:00
-- url     : https://prove2.me/submissions/1a302655-eb4d-488c-8ffc-d198752abbc8

import Mathlib
import Definitions.Def_PerishableReturns_Coordination_Model

set_option autoImplicit false
open PerishableReturns.Coordination

theorem solution (K : Costs) (c1 : ℝ) (hc : K.c < c1) (hp : c1 < K.p) :
    ∃ c2 : ℝ,
      c1 = (K.p + K.g) - (K.p + K.g2 - K.c) * (K.p + K.g - c2) / (K.p + K.g2 - K.c3) ∧
      K.c3 < c2 ∧ c2 < c1 := by
  have hg := K.g_nonneg
  have hg1 := K.g1_nonneg
  have h3 := K.c3_lt_c
  have hg2 : K.g2 = K.g + K.g1 := rfl
  have hd : 0 < K.p + K.g2 - K.c3 := by rw [hg2]; linarith
  have he : 0 < K.p + K.g2 - K.c := by rw [hg2]; linarith [K.c_lt_p]
  refine ⟨K.p + K.g - (K.p + K.g - c1) * (K.p + K.g2 - K.c3) / (K.p + K.g2 - K.c), ?_, ?_, ?_⟩
  · field_simp
    ring
  · have hnum : 0 < (K.p + K.g - K.c3) * (K.p + K.g2 - K.c)
        - (K.p + K.g - c1) * (K.p + K.g2 - K.c3) := by
      have : (K.p + K.g - K.c3) * (K.p + K.g2 - K.c)
          - (K.p + K.g - c1) * (K.p + K.g2 - K.c3)
          = (K.c - K.c3) * K.g1 + (c1 - K.c) * (K.p + K.g2 - K.c3) := by
        rw [hg2]; ring
      rw [this]
      exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) hg1) (mul_pos (by linarith) hd)
    have : K.p + K.g - (K.p + K.g - c1) * (K.p + K.g2 - K.c3) / (K.p + K.g2 - K.c) - K.c3
        = ((K.p + K.g - K.c3) * (K.p + K.g2 - K.c)
            - (K.p + K.g - c1) * (K.p + K.g2 - K.c3)) / (K.p + K.g2 - K.c) := by
      field_simp
      ring
    have h2 := div_pos hnum he
    linarith
  · have : c1 - (K.p + K.g - (K.p + K.g - c1) * (K.p + K.g2 - K.c3) / (K.p + K.g2 - K.c))
        = (K.p + K.g - c1) * (K.c - K.c3) / (K.p + K.g2 - K.c) := by
      field_simp
      rw [hg2]; ring
    have h2 : 0 < (K.p + K.g - c1) * (K.c - K.c3) / (K.p + K.g2 - K.c) :=
      div_pos (mul_pos (by linarith) (by linarith)) he
    linarith
