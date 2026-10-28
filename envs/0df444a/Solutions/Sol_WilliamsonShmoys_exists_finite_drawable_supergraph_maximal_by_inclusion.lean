-- Prove2me | solution 1 for WilliamsonShmoys.exists_finite_drawable_supergraph_maximal_by_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:06:35.297989+00:00
-- url     : https://prove2.me/submissions/a7b80524-4454-4647-953a-142f28f6307f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_max_edges
import Theorems.Thm_WilliamsonShmoys_le_of_edgeSet_ncard_le_of_le

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ M : SimpleGraph V,
      T ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by
  classical
  obtain ⟨M, hTM, hDM, hMax⟩ :=
    WilliamsonShmoys.exists_drawable_supergraph_max_edges T hT
  refine ⟨M, hTM, hDM, ?_⟩
  intro N hMN hDN
  apply WilliamsonShmoys.le_of_edgeSet_ncard_le_of_le M N hMN
  exact hMax N (le_trans hTM hMN) hDN