-- Prove2me | solution 1 for PHIP1886.incremento_A
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:03:28.295869+00:00
-- url     : https://prove2.me/submissions/ef0ae4d2-3690-44fc-b96d-53c8d1fee8d4

import Mathlib
import Definitions.Def_RHPF28_PHIP1886_559e0c85eff3
open MeasureTheory Set
open PHIP1886

theorem solution (Θ W a c : Int) :
    (4 * (Θ + a) - (W + a * c) ^ 2) - (4 * Θ - W ^ 2) = 4 * a - 2 * W * a * c - a ^ 2 * c ^ 2 := by
  grind
