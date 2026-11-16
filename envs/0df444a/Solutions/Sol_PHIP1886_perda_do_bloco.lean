-- Prove2me | solution 1 for PHIP1886.perda_do_bloco
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:03:45.509477+00:00
-- url     : https://prove2.me/submissions/93aa8841-7748-4664-acc9-e90e65593906

import Mathlib
import Definitions.Def_RHPF28_PHIP1886_559e0c85eff3
open MeasureTheory Set
open PHIP1886

theorem solution (x y : Int) : x ^ 2 + y ^ 2 - 2 * (x * y) = (y - x) ^ 2 := by
  grind
