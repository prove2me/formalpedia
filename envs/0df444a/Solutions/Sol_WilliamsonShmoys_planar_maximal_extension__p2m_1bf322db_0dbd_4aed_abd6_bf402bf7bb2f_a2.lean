-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension__p2m_1bf322db_0dbd_4aed_abd6_bf402bf7bb2f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:52:12.351219+00:00
-- url     : https://prove2.me/submissions/6e47dc0b-d07a-46ac-9ff0-f43f9a568ca9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        HasPlanarDrawingOn L →
        L.edgeSet = K.edgeSet := by
  classical
  let P : SimpleGraph V → Prop := fun G => H ≤ G ∧ HasPlanarDrawingOn G
  have hPH : P H := ⟨le_rfl, hH⟩
  obtain ⟨K, _dK, hExt⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists P).2 ⟨H, hPH⟩
  have hPK : P K := hExt.1
  refine ⟨K, ?_, hPK.2, ?_⟩
  · exact (SimpleGraph.edgeSet_subset_edgeSet).2 hPK.1
  · intro L hKL hL
    have hLK : K ≤ L := (SimpleGraph.edgeSet_subset_edgeSet).1 hKL
    have hPL : P L := ⟨hPK.1.trans hLK, hL⟩
    have hsub : K.edgeFinset ⊆ L.edgeFinset :=
      (SimpleGraph.edgeFinset_subset_edgeFinset).2 hLK
    have hcard : L.edgeFinset.card ≤ K.edgeFinset.card :=
      hExt.2 (G' := L) hPL
    have heq : K.edgeFinset = L.edgeFinset :=
      Finset.eq_of_subset_of_card_le hsub hcard
    have hEq : K = L := SimpleGraph.edgeFinset_inj.mp heq
    simpa using congrArg SimpleGraph.edgeSet hEq.symm
