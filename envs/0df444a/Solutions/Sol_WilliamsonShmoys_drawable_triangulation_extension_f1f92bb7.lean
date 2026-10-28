-- Prove2me | solution 1 for WilliamsonShmoys.drawable_triangulation_extension_f1f92bb7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:34:28.175953+00:00
-- url     : https://prove2.me/submissions/1fc53cff-e71e-4868-bcaa-a05d15e72485
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_triangulation_extension_f1f92bb7_exists_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_drawable_triangulation_extension_f1f92bb7_maximal_supergraph_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hMax⟩ :=
    WilliamsonShmoys.drawable_triangulation_extension_f1f92bb7_exists_maximal_supergraph
      L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.drawable_triangulation_extension_f1f92bb7_maximal_supergraph_edge_count
      M hM hMax hCard⟩