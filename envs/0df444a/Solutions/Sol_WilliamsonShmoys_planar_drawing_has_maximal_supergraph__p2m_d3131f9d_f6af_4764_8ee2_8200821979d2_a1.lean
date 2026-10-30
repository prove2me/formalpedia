-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_d3131f9d_f6af_4764_8ee2_8200821979d2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:05:37.352658+00:00
-- url     : https://prove2.me/submissions/24272011-906d-4889-999a-059044f22d7e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ G : SimpleGraph V,
          H ≤ G → WilliamsonShmoys.HasPlanarDrawingOn G → G = H := by
  classical
  let candidates : Set (SimpleGraph V) :=
    {G | K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have hne : candidates.Nonempty := ⟨K, le_rfl, hK⟩
  obtain ⟨H, hH, hmax⟩ :=
    Set.exists_max_image candidates (fun G => G.edgeFinset.card)
      (Set.toFinite candidates) hne
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro G hHG hG
  have hGmem : G ∈ candidates := ⟨hH.1.trans hHG, hG⟩
  have hcard : G.edgeFinset.card ≤ H.edgeFinset.card := hmax G hGmem
  have hsub : H.edgeFinset ⊆ G.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.mpr hHG
  have hedge : H.edgeFinset = G.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub hcard
  exact (SimpleGraph.edgeFinset_inj.mp hedge).symm