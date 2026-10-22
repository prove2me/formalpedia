-- Prove2me | solution 1 for WardropTraffic.EqualTimes.lt_imp_used
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:20:22.449722+00:00
-- url     : https://prove2.me/submissions/6aee36c5-1842-4160-8de4-0226dca783a4

import Mathlib
import Definitions.Def_WardropTraffic_EqualTimes_Setting

set_option autoImplicit false
open WardropTraffic.EqualTimes

theorem solution {D : ℕ} (b p : Fin D → ℝ) (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i)
    (Q t : ℝ) (q : Fin D → ℝ) (h : IsEqualTimes b p Q q t) :
    ∀ i, b i < t → 0 < q i := by
  intro i hi
  rcases lt_or_eq_of_le (h.1.1 i).1 with h0 | h0
  · exact h0
  · have := h.2.2 i h0.symm
    linarith
