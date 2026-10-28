-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_count_v2_0463fea4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:15:00.960184+00:00
-- url     : https://prove2.me/submissions/3f91defd-7daf-457f-940b-d24c3c0dda5e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_max_card_drawable_extension
import Theorems.Thm_finite_set_card_le_of_subset

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      Set.Subset Q.edgeSet R.edgeSet ∧
      ∀ S : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn S →
        Set.Subset R.edgeSet S.edgeSet →
        S.edgeSet = R.edgeSet := by
  obtain ⟨R, hR, hQR, hmax⟩ :=
    WilliamsonShmoys.exists_max_card_drawable_extension Q hQ
  refine ⟨R, hR, hQR, ?_⟩
  intro S hS hRS
  have hQS : Set.Subset Q.edgeSet S.edgeSet := hQR.trans hRS
  have hRfinite : R.edgeSet.Finite := Set.toFinite _
  have hSfinite : S.edgeSet.Finite := Set.toFinite _
  have heq : R.edgeSet = S.edgeSet :=
    finite_set_card_le_of_subset R.edgeSet S.edgeSet hRfinite hSfinite hRS
      (hmax S hS hQS)
  exact heq.symm