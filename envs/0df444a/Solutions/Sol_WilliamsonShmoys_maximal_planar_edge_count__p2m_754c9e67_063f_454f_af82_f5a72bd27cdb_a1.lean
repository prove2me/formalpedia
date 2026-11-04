-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_754c9e67_063f_454f_af82_f5a72bd27cdb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:01:20.849322+00:00
-- url     : https://prove2.me/submissions/d183c8fd-f6b3-4b22-a073-0dde75f0de12

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound__p2m_f41edfa3_d13d_40ca_8475_768212b4c7c0_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_f41edfa3_d13d_40ca_8475_768212b4c7c0_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      3 * Fintype.card V = K.edgeFinset.card + 6) := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hup := WilliamsonShmoys.planar_simple_edge_bound__p2m_f41edfa3_d13d_40ca_8475_768212b4c7c0_a1 K hV hK
  have hlo := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_f41edfa3_d13d_40ca_8475_768212b4c7c0_a1 K hV hK hmax
  omega