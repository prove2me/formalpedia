-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:43:56.92857+00:00
-- url     : https://prove2.me/submissions/fc7ba562-5ef5-4263-9b66-866f90653260

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph
import Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_has_extremal_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.inclusion_maximal_planar_has_extremal_edge_count
      K hV hK hmax⟩
