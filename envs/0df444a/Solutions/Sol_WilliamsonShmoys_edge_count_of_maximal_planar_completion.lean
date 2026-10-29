-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:17:49.407022+00:00
-- url     : https://prove2.me/submissions/e9c8fa11-e8b8-4bd1-bb28-aaa8bacd5025

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_completion
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hGK, hK, hcount⟩ :=
    WilliamsonShmoys.exists_triangulated_planar_completion G hV hG
  have hKG : K = G := hmax K hGK hK
  rw [hKG] at hcount
  exact hcount