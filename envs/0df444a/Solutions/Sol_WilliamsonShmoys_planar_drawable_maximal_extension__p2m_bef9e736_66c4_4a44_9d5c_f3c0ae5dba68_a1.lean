-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_maximal_extension__p2m_bef9e736_66c4_4a44_9d5c_f3c0ae5dba68_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:15:55.338337+00:00
-- url     : https://prove2.me/submissions/bf622a5e-cc32-4a0a-b2a6-87d08465eb3a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
      ∃ H : SimpleGraph V,
        (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
          N ≤ H ∧ HasPlanarDrawingOn H ∧
          N.edgeFinset.card ≤ H.edgeFinset.card ∧
          ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H)) := by
  classical
  let p : SimpleGraph V → Prop := fun G => N ≤ G ∧ HasPlanarDrawingOn G
  have hp : p N := ⟨le_rfl, hN⟩
  obtain ⟨H, hHdec, hExt⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 ⟨N, hp⟩
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  refine ⟨H, hExt.1.1, hExt.1.2, ?_, ?_⟩
  · exact Finset.card_mono (SimpleGraph.edgeFinset_mono hExt.1.1)
  · intro K hHK hK
    letI : DecidableRel H.Adj := hHdec
    have hPK : p K := ⟨hExt.1.1.trans hHK, hK⟩
    have hEq : H = K := (hExt.le_iff_eq hPK).mp hHK
    exact hEq.symm.le