-- Prove2me | solution 2 for WilliamsonShmoys.finite_planar_supergraph_maximal_extension_same_vertex_type
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:00:32.869583+00:00
-- url     : https://prove2.me/submissions/bef31fd6-1413-4926-9106-6817ba88c7d3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V,
        N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N := by
  classical
  have hfin : ({J : SimpleGraph V | M ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J}).Finite :=
    Set.toFinite _
  obtain ⟨N, hN⟩ := hfin.exists_maximal ⟨M, le_rfl, hM⟩
  exact ⟨N, hN.prop.1, hN.prop.2, fun K hK hPK => hN.2 ⟨le_trans hN.prop.1 hK, hPK⟩ hK⟩
