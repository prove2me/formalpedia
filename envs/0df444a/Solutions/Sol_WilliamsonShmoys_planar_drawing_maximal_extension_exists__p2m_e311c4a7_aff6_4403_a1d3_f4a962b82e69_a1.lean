-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_e311c4a7_aff6_4403_a1d3_f4a962b82e69_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:48:15.486629+00:00
-- url     : https://prove2.me/submissions/93e0b478-4c9c-4189-b80d-d19b9d9a2c66

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open Finset

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  let p : SimpleGraph V → Prop := fun K =>
    G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K
  have hex : ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, H.IsExtremal p := by
    apply (SimpleGraph.exists_isExtremal_iff_exists p).2
    exact ⟨G, le_rfl, hG⟩
  obtain ⟨H, hDec, hmax⟩ := hex
  have hGH : G ≤ H := hmax.prop.1
  have hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H := hmax.prop.2
  refine ⟨H, hGH, hHplanar, ?_, ?_⟩
  · exact Set.ncard_mono (SimpleGraph.edgeSet_mono hGH)
  · intro K hHK hKplanar
    have hcard : #K.edgeFinset ≤ #H.edgeFinset :=
      hmax.2 ⟨hGH.trans hHK, hKplanar⟩
    have heq : H.edgeFinset = K.edgeFinset :=
      Finset.eq_of_subset_of_card_le
        (SimpleGraph.edgeFinset_subset_edgeFinset.mpr hHK) hcard
    exact (SimpleGraph.edgeFinset_inj.mp heq).symm