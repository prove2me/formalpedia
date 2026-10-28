-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph_of_fintype
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:47:16.219512+00:00
-- url     : https://prove2.me/submissions/4153d0ef-aee3-45bb-a0f0-06dfe945e481

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] : Finite (SimpleGraph V) := inferInstance
