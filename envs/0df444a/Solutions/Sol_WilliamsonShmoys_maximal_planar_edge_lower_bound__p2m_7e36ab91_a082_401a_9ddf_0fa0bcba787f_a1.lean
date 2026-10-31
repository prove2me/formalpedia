-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7e36ab91_a082_401a_9ddf_0fa0bcba787f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:29:59.392892+00:00
-- url     : https://prove2.me/submissions/343b8ed7-576b-453c-a32c-4300d80261fa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_triangulated_edge_count__p2m_e0e04b13_f360_445e_bd9a_b3847171c53c_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by
  obtain ⟨K, hGK, hK, hcount⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_triangulated_edge_count__p2m_e0e04b13_f360_445e_bd9a_b3847171c53c_a1
      G hV hG
  have hKG : K = G := hmax K hGK hK
  simpa [hKG] using le_of_eq hcount