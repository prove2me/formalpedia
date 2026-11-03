-- Prove2me | solution 1 for WilliamsonShmoys.edge_card_of_inclusion_maximal_planar__p2m_bf9cfcbc_5b59_49b9_abb2_d36aa9cb22f2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:53:56.2764+00:00
-- url     : https://prove2.me/submissions/cb470aa4-edd8-4efd-a8f2-a351a1ad272b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_6a44195f_ae15_4a06_a6fa_fb89b3d5738f_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card) = 3 * Fintype.card V - 6 := by
  classical
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6a44195f_ae15_4a06_a6fa_fb89b3d5738f_a1
      H hH hcard hmax
  have hedge : H.edgeFinset.card = H.edgeSet.ncard := by
    simpa only [H.coe_edgeFinset] using (Set.ncard_coe_finset H.edgeFinset).symm
  rw [hedge]
  omega
