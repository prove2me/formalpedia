-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_for_triangulation_exact_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:53:52.37093+00:00
-- url     : https://prove2.me/submissions/5c7d632a-36c7-422a-b790-0dce94aec2c8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N := by
  classical
  let S : Set (SimpleGraph V) :=
    {K | M ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨M, le_rfl, hM⟩
  obtain ⟨N, hN, hmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨N, hN.1, hN.2, ?_⟩
  intro K hNK hK
  exact hmax ⟨hN.1.trans hNK, hK⟩ hNK