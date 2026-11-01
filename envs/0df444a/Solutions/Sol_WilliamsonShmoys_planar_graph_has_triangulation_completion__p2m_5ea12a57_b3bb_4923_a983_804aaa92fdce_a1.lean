-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulation_completion__p2m_5ea12a57_b3bb_4923_a983_804aaa92fdce_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:42:30.690665+00:00
-- url     : https://prove2.me/submissions/64646ad4-7588-4bb4-8424-9b4713878232
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_af8ffdb6_a3ca_4deb_99d5_c1621ba2f570_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_has_edge_count__p2m_af8ffdb6_a3ca_4deb_99d5_c1621ba2f570_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
        3 * Fintype.card V = M.edgeFinset.card + 6) := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension__p2m_af8ffdb6_a3ca_4deb_99d5_c1621ba2f570_a1
      L hL hcard
  have hcount :=
    WilliamsonShmoys.maximal_planar_extension_has_edge_count__p2m_af8ffdb6_a3ca_4deb_99d5_c1621ba2f570_a1
      M hM hcard hmax
  exact ⟨M, hLM, hM, hcount⟩