-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_447e7603_6167_4b10_a2c2_ce55b7ca23d6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:56:05.462309+00:00
-- url     : https://prove2.me/submissions/ecdc34fa-e0de-402c-8ac7-26aa9d763b99

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_754c9e67_063f_454f_af82_f5a72bd27cdb_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_754c9e67_063f_454f_af82_f5a72bd27cdb_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, M ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
        3 * Fintype.card V = K.edgeFinset.card + 6) := by
  obtain ⟨K, hMK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_754c9e67_063f_454f_af82_f5a72bd27cdb_a1 M hM
  refine ⟨K, hMK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_754c9e67_063f_454f_af82_f5a72bd27cdb_a1 K hV hK hmax