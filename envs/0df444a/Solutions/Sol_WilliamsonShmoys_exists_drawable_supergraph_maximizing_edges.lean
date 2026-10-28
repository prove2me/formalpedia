-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_supergraph_maximizing_edges
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:21:42.642278+00:00
-- url     : https://prove2.me/submissions/938dd001-3c1a-4453-96f3-3ca53ed0550b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_exists_maximal

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by
  let P : SimpleGraph V → Prop := fun G => L ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hP : ∃ G : SimpleGraph V, P G := ⟨L, le_rfl, hL⟩
  obtain ⟨M, hMP, hmax⟩ := WilliamsonShmoys.finite_exists_maximal
    (α := SimpleGraph V) P hP
  refine ⟨M, hMP.1, hMP.2, ?_⟩
  intro N hMN hN
  exact hmax N ⟨le_trans hMP.1 hMN, hN⟩ hMN