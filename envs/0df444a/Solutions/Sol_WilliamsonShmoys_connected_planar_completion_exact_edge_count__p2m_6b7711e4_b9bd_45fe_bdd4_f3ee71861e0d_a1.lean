-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_completion_exact_edge_count__p2m_6b7711e4_b9bd_45fe_bdd4_f3ee71861e0d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:53:54.061616+00:00
-- url     : https://prove2.me/submissions/36ff1181-3cdc-41f1-861f-e9b9565af17c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_exists__p2m_bd02a62a_20ac_45ba_a540_81b91c2ce75e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count__p2m_bd02a62a_20ac_45ba_a540_81b91c2ce75e_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) (hConn : K.Connected) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      3 * Fintype.card V - 6 = H.edgeSet.ncard := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_bd02a62a_20ac_45ba_a540_81b91c2ce75e_a1 K hK hV hConn
  exact ⟨H, hKH, hH,
    WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_bd02a62a_20ac_45ba_a540_81b91c2ce75e_a1 H hH hmax hV⟩