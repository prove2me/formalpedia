-- Prove2me | solution 1 for WilliamsonShmoys_planar_edge_count_upper_bound__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:04:41.085999+00:00
-- url     : https://prove2.me/submissions/086b6bec-9abe-4e34-8f1e-98edebddb51a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_completion__p2m_1313175c_9801_43ac_98ea_21e1b7fe79cc_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  classical
  letI : DecidableRel G.Adj := dG
  obtain ⟨H, dH, hsub, hcard⟩ :=
    WilliamsonShmoys_planar_graph_has_triangulated_completion__p2m_1313175c_9801_43ac_98ea_21e1b7fe79cc_a2
      G hG hV
  letI : DecidableRel H.Adj := dH
  calc
    G.edgeFinset.card ≤ H.edgeFinset.card := Finset.card_le_card hsub
    _ = 3 * Fintype.card V - 6 := hcard