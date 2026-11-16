-- Prove2me | solution 1 for PHIP1886.cruzamento
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:03:53.977674+00:00
-- url     : https://prove2.me/submissions/d72a6a28-22aa-4aae-99a0-3c14a6c12d6f

import Mathlib
import Definitions.Def_RHPF28_PHIP1886_559e0c85eff3
open MeasureTheory Set
open PHIP1886

theorem solution (α β : Int) : 2 * (β - α) * β - (β ^ 2 - α ^ 2) = (β - α) ^ 2 := by
  grind
