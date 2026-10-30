-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_54a0e51c_08bc_41d0_9e00_f8ba78b35c82
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:21:12.232504+00:00
-- url     : https://prove2.me/submissions/cb863b63-6d02-4b42-b344-443783b55600

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_for_maximal_edge_count_54a0e51c

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_for_maximal_edge_count_54a0e51c K hK hV
  have hLK : L.edgeSet ⊆ K.edgeSet := hmax L hKL hL
  have heq : K.edgeSet = L.edgeSet := Set.Subset.antisymm hKL hLK
  rw [heq]
  exact hcount