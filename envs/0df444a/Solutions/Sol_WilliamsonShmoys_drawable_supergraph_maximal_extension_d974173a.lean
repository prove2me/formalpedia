-- Prove2me | solution 1 for WilliamsonShmoys.drawable_supergraph_maximal_extension_d974173a
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:17:34.78506+00:00
-- url     : https://prove2.me/submissions/1d173d3c-0043-4759-b9e5-a60a25e060f5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_max_edge_count
import Theorems.Thm_WilliamsonShmoys_edge_count_lt_of_lt

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_drawable_supergraph_max_edge_count H hdraw
  refine ⟨K, hHK, hK, ?_⟩
  intro L hKL hL
  by_contra hneq
  have hstrict : K < L :=
    lt_of_le_of_ne hKL (by
      intro h
      exact hneq h.symm)
  have hcardlt := WilliamsonShmoys.edge_count_lt_of_lt K L hstrict
  have hcardle := hmax L (le_trans hHK hKL) hL
  exact (Nat.not_lt_of_ge hcardle hcardlt).elim
