-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_lower_bound__p2m_f02ef8ad_5db5_4334_91a0_6b5d944fa80f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T12:21:28.652585+00:00
-- url     : https://prove2.me/submissions/b5112d72-d489-4aa0-a2f2-c477f6f88fc3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_edge_count__p2m_f3d5ae7b_e757_4e01_bdda_63180755b949_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeSet ⊆ L.edgeSet →
      L.edgeSet ⊆ K.edgeSet) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hL, hKL, hcount⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_edge_count__p2m_f3d5ae7b_e757_4e01_bdda_63180755b949_a1
      K hK hV
  have hLK : L.edgeSet ⊆ K.edgeSet := hmax L hL hKL
  have hsets : K.edgeSet = L.edgeSet := Set.Subset.antisymm hKL hLK
  simpa [hsets] using (le_of_eq hcount.symm)
