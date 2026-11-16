-- Prove2me | solution 1 for PHIP1886.folga_quadratica
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:03:36.625357+00:00
-- url     : https://prove2.me/submissions/8a2a4d06-cd0c-438f-9928-87cc036e4cb8

import Mathlib
import Definitions.Def_RHPF28_PHIP1886_559e0c85eff3
open MeasureTheory Set
open PHIP1886

theorem solution (s T : Int) : s * s + T * T - 2 * T * s = (s - T) ^ 2 := by
  grind
