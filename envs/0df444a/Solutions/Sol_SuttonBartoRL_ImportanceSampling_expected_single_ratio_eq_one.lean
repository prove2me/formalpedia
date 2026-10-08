-- Prove2me | solution 1 for SuttonBartoRL.ImportanceSampling.expected_single_ratio_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T10:25:47.742752+00:00
-- url     : https://prove2.me/submissions/5bf2fae8-4fe0-4fc1-99b3-887804c54853

import Mathlib
import Definitions.Def_SuttonBartoRL_ImportanceSampling_MDP

set_option autoImplicit false

open SuttonBartoRL.ImportanceSampling in
theorem solution {S A : Type} [Fintype A]
    (π b : SuttonBartoRL.FiniteMDP.Policy S A) (hcov : Coverage π b) (x : S) :
    ∑ a, b.prob x a * (π.prob x a / b.prob x a) = ∑ a, π.prob x a ∧
    ∑ a, π.prob x a = 1 := by
  refine ⟨?_, π.sum_one x⟩
  refine Finset.sum_congr rfl fun a _ => ?_
  rcases (b.nonneg x a).lt_or_eq with hb | hb
  · field_simp
  · have hπ : π.prob x a = 0 := by
      rcases (π.nonneg x a).lt_or_eq with hp | hp
      · exact absurd (hcov x a hp) (by rw [← hb]; exact lt_irrefl 0)
      · exact hp.symm
    rw [← hb, hπ]; simp
