-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_12627fe4_bb8b_4611_a4bf_2ba10834172b
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:53:39.25799+00:00
-- url     : https://prove2.me/submissions/4b74fb35-15bf-49dc-b499-59eea5d7afbc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulation_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hMdraw, hCount⟩ :=
    WilliamsonShmoys.exists_triangulation_completion L hLdraw hCard
  have hML : M ≤ L := hMax M hLM hMdraw
  have hCountL : L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
    simpa [le_antisymm hML hLM] using hCount
  omega