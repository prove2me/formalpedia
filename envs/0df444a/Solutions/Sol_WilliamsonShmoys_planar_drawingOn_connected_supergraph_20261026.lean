-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_connected_supergraph_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:38:59.520665+00:00
-- url     : https://prove2.me/submissions/fa885593-d6c3-43d8-a7d7-aa010af3cbd3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_exists_20261026
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_connected_20261026

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K' : SimpleGraph V,
      K ≤ K' ∧ K'.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K' := by
  obtain ⟨K', hKK', hK'draw, hK'max⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph_exists_20261026 K hK
  refine ⟨K', hKK', ?_, hK'draw⟩
  exact WilliamsonShmoys.planar_maximal_supergraph_connected_20261026
    K' hK'draw hK'max hV