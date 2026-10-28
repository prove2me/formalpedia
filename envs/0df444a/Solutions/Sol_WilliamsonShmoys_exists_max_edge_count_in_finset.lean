-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_edge_count_in_finset
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:56:25.270494+00:00
-- url     : https://prove2.me/submissions/03bcdd8e-9098-4f45-ae47-0bd5d2b74f6c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : Finset (SimpleGraph V)) (hS : S.Nonempty) :
    ∃ H ∈ S, ∀ J ∈ S, J.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Finset.exists_max_image S (fun G => G.edgeSet.ncard) hS