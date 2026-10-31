-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_7e28d180_08cc_4953_8752_6b4f2973fe5d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:29:07.17767+00:00
-- url     : https://prove2.me/submissions/8d17b373-3549-4d52-816a-ecd1a4f4065e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension__p2m_152d6993_7004_4697_ab26_f8c2f883dc25_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ S : SimpleGraph V, M ≤ S → WilliamsonShmoys.HasPlanarDrawingOn S → S ≤ M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨S, hMS, hSPlanar, hSEdges⟩ :=
    WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_152d6993_7004_4697_ab26_f8c2f883dc25_a1
      M hM hCard
  have hSM : S ≤ M := hMax S hMS hSPlanar
  have hEq : S = M := le_antisymm hSM hMS
  simpa [hEq] using hSEdges