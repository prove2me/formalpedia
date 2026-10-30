-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_729fc1e5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:36:04.928045+00:00
-- url     : https://prove2.me/submissions/99c1773d-7e3f-456a-9e21-bb0f9de521cf

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_repair2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_repair2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hE : R.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ S : SimpleGraph V, R ≤ S ∧ S ≠ R ∧
      WilliamsonShmoys.HasPlanarDrawingOn S := by
  obtain ⟨S, hRS, hS, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_repair2 R hR
  have hcount := WilliamsonShmoys.maximal_planar_edge_count_repair2 S hV hS hmax
  refine ⟨S, hRS, ?_, hS⟩
  intro hSR
  have hRcount : R.edgeSet.ncard = 3 * Fintype.card V - 6 := by
    simpa [hSR] using hcount
  omega