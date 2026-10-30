-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_inclusion_maximal_edge_count__p2m_a983af35_26d8_44a9_8810_a80e355bc9cf_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:19:04.559933+00:00
-- url     : https://prove2.me/submissions/0d17d67e-f12d-481c-8f4b-885c25f6117a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_sharp_edge_count__p2m_4dcc8868_a279_4e00_9c27_a17d1a75556d_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hU : HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V, U ≤ W → HasPlanarDrawingOn W → W ≤ U) :
    3 * Fintype.card V - 6 = U.edgeSet.ncard := by
  obtain ⟨W, hUW, hW, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_with_sharp_edge_count__p2m_4dcc8868_a279_4e00_9c27_a17d1a75556d_a1
      U hV hU
  have hWU : W ≤ U := hmax W hUW hW
  have hEq : W = U := le_antisymm hWU hUW
  simpa [hEq] using hcount