-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_lower_bound_of_maximal_planar_drawing_via_threshold_euler
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:47:27.732322+00:00
-- url     : https://prove2.me/submissions/a8c45c18-f01e-4fd6-a732-fd67632c1459
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨N, hMN, hN, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count M hV hM
  have hNM : N = M := hmax N hMN hN
  simpa [hNM] using hcount.le