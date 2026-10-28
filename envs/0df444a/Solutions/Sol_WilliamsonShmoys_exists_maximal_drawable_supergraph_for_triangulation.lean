-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph_for_triangulation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:00:59.904054+00:00
-- url     : https://prove2.me/submissions/16803ca6-5528-49f1-9fbb-1c9487acbf30

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_subgraph_property

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by
  obtain ⟨L, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_subgraph_property
      (fun G : SimpleGraph V => K ≤ G ∧ HasPlanarDrawingOn G)
      ⟨K, le_rfl, hK⟩
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hLM hM
  exact hmax M ⟨hL.1.trans hLM, hM⟩ hLM