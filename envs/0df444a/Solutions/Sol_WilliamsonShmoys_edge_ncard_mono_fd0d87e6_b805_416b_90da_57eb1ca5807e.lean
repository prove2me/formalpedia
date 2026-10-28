-- Prove2me | solution 1 for WilliamsonShmoys.edge_ncard_mono_fd0d87e6_b805_416b_90da_57eb1ca5807e
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T10:48:56.991011+00:00
-- url     : https://prove2.me/submissions/c99cc7fe-238b-45b1-a62c-b41b2c6e7459

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)
