-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_6f52b5a3_b090_4468_aa84_13620a15b574_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:59:35.047916+00:00
-- url     : https://prove2.me/submissions/00517519-616d-4ac2-945f-633ee38e8754

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_ccb6a6bc_2d03_4d79_9277_48639c2dde63_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, Set.Subset N.edgeSet P.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = N)
    (hCard : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨P, hsub, hP, hcount⟩ :=
    WilliamsonShmoys.planar_completion_edge_count__p2m_ccb6a6bc_2d03_4d79_9277_48639c2dde63_a1
      N hN hCard
  have hPN : P = N := hmax P hsub hP
  subst P
  exact hcount