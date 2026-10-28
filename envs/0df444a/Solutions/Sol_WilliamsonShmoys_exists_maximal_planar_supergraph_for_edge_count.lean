-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:28:12.394685+00:00
-- url     : https://prove2.me/submissions/621d059f-0712-4ce7-a3d4-3d9be8ae5394

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_exists_maximum_edge_count_drawable_supergraph
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_lt_of_le_ne

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ H' : SimpleGraph V,
        H ≤ H' → WilliamsonShmoys.HasPlanarDrawingOn H' → H' = H) ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximum_edge_count_drawable_supergraph K hK
  refine ⟨H, hKH, hH, ?_, ?_⟩
  · intro H' hHH' hH'
    have hKH' : K ≤ H' := le_trans hKH hHH'
    by_contra hne
    have hlt := WilliamsonShmoys.edgeSet_ncard_lt_of_le_ne hHH' (Ne.symm hne)
    have hle := hmax H' hKH' hH'
    omega
  · by_cases hEq : K = H
    · simpa [hEq]
    · exact le_of_lt (WilliamsonShmoys.edgeSet_ncard_lt_of_le_ne hKH hEq)