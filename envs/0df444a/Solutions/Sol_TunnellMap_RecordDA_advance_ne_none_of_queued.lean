-- Prove2me | solution 1 for TunnellMap.RecordDA.advance_ne_none_of_queued
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:27:36.453648+00:00
-- url     : https://prove2.me/submissions/b23e6066-4cc7-4e6d-9aca-254c41b8bbff

import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Theorems.Thm_TunnellMap_BlockGen_advance_eq_none
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_queued_cursor_lt


set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    {E : DARun n} (hSim : Sim hnpos frames E)
    (hv : (abst hn hnpos frames E).Valid (residualOrbitRanking hnpos))
    (s : BResidual n) (hs : s ∈ E.queue) :
    BlockGen.advance s (frames s) (E.gen s) ≠ none := by
  intro hadv
  have hqabs : orbOf s ∈ (abst hn hnpos frames E).queue := by
    rw [abst_queue]; exact List.mem_map_of_mem hs
  have hlt := DAState.queued_cursor_lt _ hcard _ hv (orbOf s) hqabs
  rw [abst_cursor, hSim.canon s (hSim.queue_sub s hs)] at hlt
  have hrem : remainingTrace s (frames s) (E.gen s) = [] := advance_eq_none _ hadv
  rw [cursorOf, hrem, List.length_nil, Nat.sub_zero,
    fullTrace_length_card hn hnpos s (frames s)] at hlt
  exact lt_irrefl _ hlt
end TunnellMap.RecordDA
