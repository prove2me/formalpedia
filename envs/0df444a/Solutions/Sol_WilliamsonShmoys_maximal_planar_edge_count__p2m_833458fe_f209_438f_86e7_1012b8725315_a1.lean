-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_833458fe_f209_438f_86e7_1012b8725315_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:52:18.65447+00:00
-- url     : https://prove2.me/submissions/5ed41318-7ddf-442d-8dd4-d2ae2d0596dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_620608d3_0799_426b_beeb_eff4e8e41716_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_620608d3_0799_426b_beeb_eff4e8e41716_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, HasPlanarDrawingOn L →
      (∀ u v, K.Adj u v → L.Adj u v) → L = K)
    (hcard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper :=
    WilliamsonShmoys.planar_edge_count_upper__p2m_620608d3_0799_426b_beeb_eff4e8e41716_a1
      K hK hcard
  have hlower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_620608d3_0799_426b_beeb_eff4e8e41716_a1
      K hK hmax hcard
  omega