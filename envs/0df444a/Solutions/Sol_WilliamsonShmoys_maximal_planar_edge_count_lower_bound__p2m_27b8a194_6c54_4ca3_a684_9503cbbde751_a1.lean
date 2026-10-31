-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_27b8a194_6c54_4ca3_a684_9503cbbde751_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:38:05.632714+00:00
-- url     : https://prove2.me/submissions/b60d02d7-cfa0-40de-a2ee-ae0c8e1650a8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_3060859a_0839_41c9_be06_b54269f75aee_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, J ≤ K → HasPlanarDrawingOn K → K ≤ J) :
    3 * Fintype.card V ≤ J.edgeSet.ncard + 6 := by
  obtain ⟨N, hJN, hNPlanar, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_3060859a_0839_41c9_be06_b54269f75aee_a1
      J hV hPlanar
  have hNJ : N ≤ J := hMax N hJN hNPlanar
  have hEq : J = N := le_antisymm hJN hNJ
  have hEdges : J.edgeSet.ncard = N.edgeSet.ncard :=
    congrArg (fun G : SimpleGraph V => G.edgeSet.ncard) hEq
  omega
