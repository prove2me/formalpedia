-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_7bba71c9_ccd8_4c5e_9f36_6c106eba0d6c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:40:35.009344+00:00
-- url     : https://prove2.me/submissions/9bd96bf5-79ec-4970-b739-90f1be4320ec

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hconn : N.Connected) (hN : HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     ∃ H : SimpleGraph V, N ≤ H ∧ HasPlanarDrawingOn H ∧
       (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) ∧
       (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
        N.edgeFinset.card ≤ H.edgeFinset.card)) := by
  classical
  let p : SimpleGraph V → Prop := fun G => N ≤ G ∧ HasPlanarDrawingOn G
  have hex : ∃ G : SimpleGraph V, p G := ⟨N, le_rfl, hN⟩
  obtain ⟨H, hDecH, hExt⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 hex
  have hprop : N ≤ H ∧ HasPlanarDrawingOn H := hExt.1
  refine ⟨H, hprop.1, hprop.2, ?_, ?_⟩
  · intro K hHK hK
    have hKprop : p K := ⟨hprop.1.trans hHK, hK⟩
    have hEq : H = K := by
      letI : DecidableRel H.Adj := hDecH
      exact (SimpleGraph.IsExtremal.le_iff_eq hExt hKprop).mp hHK
    exact hEq.symm
  · letI : DecidableRel N.Adj := Classical.decRel N.Adj
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hprop.1)