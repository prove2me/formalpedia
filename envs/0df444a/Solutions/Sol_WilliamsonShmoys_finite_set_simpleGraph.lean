-- Prove2me | solution 1 for WilliamsonShmoys.finite_set_simpleGraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:03:08.113993+00:00
-- url     : https://prove2.me/submissions/6e20e203-56b0-474e-8a43-40d54eda9081

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] (s : Set (SimpleGraph V)) :
    s.Finite := by
  classical
  exact Set.toFinite s