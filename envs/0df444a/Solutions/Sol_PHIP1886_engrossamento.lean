-- Prove2me | solution 1 for PHIP1886.engrossamento
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:10:50.937207+00:00
-- url     : https://prove2.me/submissions/b3a1c431-2e5e-44f9-9c5c-5d63f1fa1dbc

import Mathlib
import Definitions.Def_RHPF28_PHIP1886_559e0c85eff3
open MeasureTheory Set
open PHIP1886

theorem solution (h u : Int) (hh : 0 ≤ h) :
    hat (2 * h) u = hat h (u - h) + 2 * hat h u + hat h (u + h) := by
  unfold hat; omega
