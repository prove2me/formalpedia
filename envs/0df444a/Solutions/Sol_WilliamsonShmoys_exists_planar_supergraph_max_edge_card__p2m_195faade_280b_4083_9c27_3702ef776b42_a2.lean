-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_max_edge_card__p2m_195faade_280b_4083_9c27_3702ef776b42_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:03:32.258529+00:00
-- url     : https://prove2.me/submissions/d7f13fae-4548-4409-8d6f-53dac315d9dc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_max_nat_on_finite_predicate__p2m_c1b261ba_306d_4a6e_a5c0_9da269f5f325_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      Q ≤ R ∧ WilliamsonShmoys.HasPlanarDrawingOn R ∧
      (∀ S : SimpleGraph V, Q ≤ S → WilliamsonShmoys.HasPlanarDrawingOn S →
        S.edgeSet.ncard ≤ R.edgeSet.ncard) := by
  classical
  let P : SimpleGraph V → Prop := fun S => Q ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S
  have hP : ∃ S, P S := ⟨Q, le_rfl, hDraw⟩
  obtain ⟨R, hR, hmax⟩ :=
    exists_max_nat_on_finite_predicate__p2m_c1b261ba_306d_4a6e_a5c0_9da269f5f325_a1
      P hP (fun S => S.edgeSet.ncard)
  exact ⟨R, hR.1, hR.2, fun S hQS hSdraw => hmax S ⟨hQS, hSdraw⟩⟩