-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_ef8dab25_617a_4455_968a_bd2c49e19056_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:34:11.473339+00:00
-- url     : https://prove2.me/submissions/9b8a57a2-3a4e-408c-9c28-e888c3ad4ce5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_649933f7_19ec_4f62_a5e6_2469237e8943_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_649933f7_19ec_4f62_a5e6_2469237e8943_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    (letI : DecidableRel M.Adj := dM
     M.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  letI : DecidableRel M.Adj := dM
  have hup := WilliamsonShmoys.planar_edge_count_upper__p2m_649933f7_19ec_4f62_a5e6_2469237e8943_a1 M dM hM hcard
  have hlo := WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_649933f7_19ec_4f62_a5e6_2469237e8943_a1 M dM hM hcard hmax
  omega