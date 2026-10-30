-- Prove2me | solution 1 for WilliamsonShmoys.finite_set_of_planar_drawings__p2m_a402c68a_d7fd_45a8_9fd3_2080e97d0c7e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:29:54.006969+00:00
-- url     : https://prove2.me/submissions/299a375c-0560-457a-b9b6-8ac85596d341

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] :
    ({N : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn N} : Set (SimpleGraph V)).Finite := by
  classical
  exact Set.toFinite _