-- Prove2me | solution 1 for PHIP1886.fatoracao_A
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:03:17.223047+00:00
-- url     : https://prove2.me/submissions/8c19080c-80c4-42c7-8cff-0126774f7cc0

import Mathlib
import Definitions.Def_RHPF28_PHIP1886_559e0c85eff3
open MeasureTheory Set
open PHIP1886

theorem solution (T W : Int) : 4 * T ^ 2 - W ^ 2 = (2 * T - W) * (2 * T + W) := by
  grind
