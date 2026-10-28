-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_card_drawable_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T13:03:00.970575+00:00
-- url     : https://prove2.me/submissions/0c5315ef-327a-450f-ac2a-5a9b4e53a296

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      Set.Subset Q.edgeSet R.edgeSet ∧
      ∀ S : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn S →
        Set.Subset Q.edgeSet S.edgeSet →
        S.edgeSet.ncard ≤ R.edgeSet.ncard := by
  classical
  have hfin : ({J : SimpleGraph V | Q ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J}).Finite :=
    Set.toFinite _
  obtain ⟨M, hM, hmax⟩ := Set.exists_max_image _ (fun J : SimpleGraph V => J.edgeSet.ncard) hfin
    ⟨Q, le_rfl, hQ⟩
  exact ⟨M, hM.2, SimpleGraph.edgeSet_subset_edgeSet.2 hM.1,
    fun S hS hQS => hmax S ⟨SimpleGraph.edgeSet_subset_edgeSet.1 hQS, hS⟩⟩
