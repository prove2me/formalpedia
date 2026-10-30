-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_fc022252_a12f_4a07_aef3_b2bbba00d482_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:42:04.991236+00:00
-- url     : https://prove2.me/submissions/b7f8c56c-ef06-45c8-9ed8-a14cb20c966f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_same_vertex_set__p2m_b07b2cea_077c_4214_a610_9ab8bd281015_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_b07b2cea_077c_4214_a610_9ab8bd281015_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    exists L : SimpleGraph V,
      K <= L ∧ HasPlanarDrawingOn L ∧
        (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
         L.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨L, hKL, hLplanar, hLmax⟩ :=
    WilliamsonShmoys.planar_maximal_extension_same_vertex_set__p2m_b07b2cea_077c_4214_a610_9ab8bd281015_a1
      K hK hcard
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_b07b2cea_077c_4214_a610_9ab8bd281015_a1
      L hLplanar hcard hLmax
  exact ⟨L, hKL, hLplanar, hcount⟩