-- Prove2me | solution 1 for WilliamsonShmoys_edge_maximal_planar_extension__p2m_e657dedf_589f_4338_b1cf_3cbd004df18d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:01:56.828496+00:00
-- url     : https://prove2.me/submissions/fe765923-4fc6-46f2-a3ec-81e339145bf3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ K.Connected ∧
      (∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  classical
  let P : SimpleGraph V → Prop := fun G => H ≤ G ∧ HasPlanarDrawingOn G
  have hP : ∃ G : SimpleGraph V, P G := ⟨H, le_rfl, hH⟩
  obtain ⟨K, hdec, hK⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists P).2 hP
  letI := hdec
  refine ⟨K, hK.prop.1, hK.prop.2,
    SimpleGraph.Connected.mono hK.prop.1 hconn, ?_, ?_⟩
  · intro L hKL hL
    have hPL : P L := ⟨hK.prop.1.trans hKL, hL⟩
    have hcard : L.edgeFinset.card ≤ K.edgeFinset.card := hK.2 hPL
    have hsubset : K.edgeFinset ⊆ L.edgeFinset :=
      SimpleGraph.edgeFinset_subset_edgeFinset.2 hKL
    have hedge : K.edgeFinset = L.edgeFinset :=
      Finset.eq_of_subset_of_card_le hsubset hcard
    exact SimpleGraph.edgeFinset_inj.mp hedge.symm
  · exact Set.ncard_mono (SimpleGraph.edgeSet_subset_edgeSet.mpr hK.prop.1)
