-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_edge_count_lower_from_triangulation_c132589d_retry3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:04:19.4446+00:00
-- url     : https://prove2.me/submissions/8837dd54-eb91-46c6-8119-bc83b51a43b0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion
import Theorems.Thm_WilliamsonShmoys_edge_card_mono_of_adj_inclusion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      (∀ u v, L.Adj u v → M.Adj u v) →
      HasPlanarDrawingOn M →
      ∀ u v, M.Adj u v → L.Adj u v) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hMDraw, hMCard⟩ :=
    WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion L hDraw hCard
  have hML : ∀ u v, M.Adj u v → L.Adj u v := by
    intro u v huv
    exact hMax M (fun a b hab => hLM hab) hMDraw u v huv
  have hEdgeCard :=
    WilliamsonShmoys.edge_card_mono_of_adj_inclusion M L hML
  have hMNat : M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
    omega
  rw [hMNat] at hEdgeCard
  omega