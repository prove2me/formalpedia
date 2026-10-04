-- Prove2me | solution 1 for TaoFivePrimes.eta1_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-08T09:13:30.985559+00:00
-- url     : https://prove2.me/submissions/99cc7fed-2f36-4dcc-8e8a-f5a207add9b5

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open TaoFivePrimes

theorem solution (t : ℝ) : 0 ≤ eta1 t := le_max_left _ _
