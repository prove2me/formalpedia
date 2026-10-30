-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_ffbccb21_453c_4aae_b4fb_4ee36a71a8e5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:10:11.444922+00:00
-- url     : https://prove2.me/submissions/5d47786e-de50-486d-8460-97429cd5966f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hDraw : HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V,
      N ≤ H ∧ HasPlanarDrawingOn H ∧
      N.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) := by
  classical
  obtain ⟨H, hNH, hMax⟩ :=
    Finite.exists_le_maximal (p := fun G : SimpleGraph V => HasPlanarDrawingOn G) hDraw
  refine ⟨H, hNH, hMax.prop, ?_, ?_⟩
  · apply Set.ncard_mono
    exact (SimpleGraph.edgeSet_subset_edgeSet).2 hNH
  · intro K hHK hKDraw
    exact (hMax.eq_of_le hKDraw hHK).symm