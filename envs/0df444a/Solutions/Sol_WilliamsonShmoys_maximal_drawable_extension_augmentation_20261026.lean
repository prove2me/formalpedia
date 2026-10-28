-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_extension_augmentation_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:58:05.868901+00:00
-- url     : https://prove2.me/submissions/2c7d0342-29c5-43ae-b036-54251d5f3ddd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_20261026
import Theorems.Thm_WilliamsonShmoys_subgraph_strict_of_edgeSet_ncard_lt_20261026

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hE : L.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ M : SimpleGraph V, L < M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M := by
  obtain ⟨M, hLM, hM, hMc⟩ :=
    WilliamsonShmoys.planar_triangulation_completion_20261026 L hL hV
  have hcount : L.edgeSet.ncard < M.edgeSet.ncard := by
    rw [hMc]
    exact hE
  have hstrict := WilliamsonShmoys.subgraph_strict_of_edgeSet_ncard_lt_20261026
    L M hLM hcount
  exact ⟨M, hstrict, hM⟩