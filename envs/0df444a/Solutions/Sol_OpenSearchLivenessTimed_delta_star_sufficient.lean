-- Prove2me | solution 1 for OpenSearchLivenessTimed.delta_star_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T18:53:49.650873+00:00
-- url     : https://prove2.me/submissions/4d704522-e807-4b5c-9ea5-53ee14cba3ae

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

theorem solution (t0 D P δ win competitor : Int)
    (hwin : win ≤ t0 + 4 * D + P) (hcomp : t0 + δ ≤ competitor)
    (hδ : 4 * D + P < δ) : win < competitor := by
  omega
