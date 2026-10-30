-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_with_sharp_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:35:24.963982+00:00
-- url     : https://prove2.me/submissions/c55842cf-a96d-4090-b07b-fa33782fb52e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_maximal_by_inclusion_16efa91f_ea17_4fca_8681_329f091064c3
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_lower_bound_16efa91f_ea17_4fca_8681_329f091064c3
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_16efa91f_ea17_4fca_8681_329f091064c3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    exists M : SimpleGraph V, L <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hMax⟩ :=
    WilliamsonShmoys.planar_extension_maximal_by_inclusion_16efa91f_ea17_4fca_8681_329f091064c3
      L hL
  have hLower :=
    WilliamsonShmoys.maximal_drawing_edge_lower_bound_16efa91f_ea17_4fca_8681_329f091064c3
      M hV hM hMax
  have hUpper :=
    WilliamsonShmoys.planar_drawing_edge_upper_bound_16efa91f_ea17_4fca_8681_329f091064c3
      M hV hM
  refine ⟨M, hLM, hM, ?_⟩
  omega
