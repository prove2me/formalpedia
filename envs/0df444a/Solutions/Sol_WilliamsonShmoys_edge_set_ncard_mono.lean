-- Prove2me | solution 1 for WilliamsonShmoys.edge_set_ncard_mono
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:38:51.27251+00:00
-- url     : https://prove2.me/submissions/3a13cc65-1a9f-414b-bbee-c01080631f0a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hsub : ∀ u v, G.Adj u v → H.Adj u v) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_mono (fun u v h => hsub u v h)) (Set.toFinite _)
