-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_mono_of_subgraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T03:17:29.697145+00:00
-- url     : https://prove2.me/submissions/09323211-3295-4cd0-8092-2405b718e0ab

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution {V : Type} [Fintype V] [LinearOrder V] (H K : SimpleGraph V) (hHK : H ≤ K) : H.edgeSet.ncard ≤ K.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hHK) (Set.toFinite _)
