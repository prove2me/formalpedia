-- Prove2me | solution 1 for WardropTraffic.EqualTimes.used_imp_lt
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:18:10.260437+00:00
-- url     : https://prove2.me/submissions/9823af22-8d81-4bb9-a411-526591dc11e2

import Mathlib
import Definitions.Def_WardropTraffic_EqualTimes_Setting

set_option autoImplicit false
open WardropTraffic.EqualTimes

theorem solution {D : ℕ} (b p : Fin D → ℝ) (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i)
    (Q t : ℝ) (q : Fin D → ℝ) (h : IsEqualTimes b p Q q t) :
    ∀ i, 0 < q i → b i < t := by
  intro i hi
  have hq := h.2.1 i hi
  have hlt : q i < p i := (h.1.1 i).2
  have h1 : 0 < 1 - q i / p i := by
    have : q i / p i < 1 := (div_lt_one (hp i)).2 hlt
    linarith
  have h2 : 1 - q i / p i < 1 := by
    have : 0 < q i / p i := div_pos hi (hp i)
    linarith
  unfold routeTime at hq
  rw [← hq]
  rw [lt_div_iff₀ h1]
  nlinarith [hb i]
