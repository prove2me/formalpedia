-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_maximal_supergraph__p2m_2b94d345_c453_470c_8517_8648e22306c1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:28:17.958638+00:00
-- url     : https://prove2.me/submissions/52da23cf-1be4-4394-971c-0cf827d08d4a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ L : SimpleGraph V, H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ K : SimpleGraph V, L ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ L := by
  classical
  let eligible : Set (SimpleGraph V) :=
    {L | H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L}
  have hfinite : eligible.Finite := Set.toFinite eligible
  have hnonempty : eligible.Nonempty := ⟨H, le_rfl, hH⟩
  obtain ⟨L, hLmax⟩ := hfinite.exists_maximal hnonempty
  have hL : H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L := hLmax.1
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro K hLK hK
  have hKeligible : eligible K := ⟨hL.1.trans hLK, hK⟩
  exact hLmax.2 hKeligible hLK