-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_6cac0be3_cdae_42f1_a688_5a8b1965052e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:48:41.85849+00:00
-- url     : https://prove2.me/submissions/bd5fdfc5-2a11-401c-b757-774fec9a3e8f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_40d66966_5ea4_40f0_a08a_acc21533796c_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn H)
    (hMax : forall J : SimpleGraph V, H <= J -> HasPlanarDrawingOn J -> J = H)
    (hConn : H.Connected)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by
  obtain ⟨J, hSub, hPlanarJ, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_40d66966_5ea4_40f0_a08a_acc21533796c_a2
      H hPlanar hV
  have hEq : J = H := hMax J hSub hPlanarJ
  have hCountH : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
    simpa [hEq] using hCount
  omega