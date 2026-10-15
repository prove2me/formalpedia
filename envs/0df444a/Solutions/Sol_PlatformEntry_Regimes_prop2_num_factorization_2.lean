-- Prove2me | solution 2 for PlatformEntry.Regimes.prop2_num_factorization
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T13:50:05.318644+00:00
-- url     : https://prove2.me/submissions/dadc6b1b-6b99-48b1-a3a2-ee724eb69dc6

import Mathlib
import Definitions.Def_PlatformEntry_Regimes_Model
open PlatformEntry.Regimes

theorem solution(δ f β : ℝ) :
    4 * N5 δ f β ^ 2 - D δ f β ^ 2 = P11 δ f β * S2 δ f β := by
  unfold N5 D P11 S2
  ring
