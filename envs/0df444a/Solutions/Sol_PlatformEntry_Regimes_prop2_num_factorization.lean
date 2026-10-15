-- Prove2me | solution 1 for PlatformEntry.Regimes.prop2_num_factorization
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T13:50:05.007259+00:00
-- url     : https://prove2.me/submissions/bb433677-5d1b-4477-9838-9e8eb6d81f1b

import Mathlib
import Definitions.Def_PlatformEntry_Regimes_Model
open PlatformEntry.Regimes

theorem solution(δ f β : ℝ) :
    4 * N5 δ f β ^ 2 - D δ f β ^ 2 = P11 δ f β * S2 δ f β := by
  unfold N5 D P11 S2
  ring
