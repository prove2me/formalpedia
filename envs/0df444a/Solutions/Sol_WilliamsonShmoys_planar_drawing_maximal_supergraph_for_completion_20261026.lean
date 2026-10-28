-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_for_completion_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:15:19.254693+00:00
-- url     : https://prove2.me/submissions/fac9e486-62cf-4a0c-b54b-2ca9aa4d7e3e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_max_ncard_planar_supergraph_20261026
import Theorems.Thm_WilliamsonShmoys_ncard_lt_of_strict_le_20261026

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N →
          WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_max_ncard_planar_supergraph_20261026 L hL
  refine ⟨M, hLM, hM, ?_⟩
  intro N hMN hN
  have hLN : L ≤ N := hLM.trans hMN
  by_contra hne
  have hlt : M.edgeSet.ncard < N.edgeSet.ncard :=
    WilliamsonShmoys.ncard_lt_of_strict_le_20261026 M N hMN hne
  exact (not_lt_of_ge (hmax N hLN hN)) hlt