-- Prove2me | solution 1 for WilliamsonShmoys.maximalPlanarDrawingOn_edge_count_e1b54b32
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:55:08.659838+00:00
-- url     : https://prove2.me/submissions/89f4f0df-5e32-414f-b673-0835c0c17bc3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_for_edge_count_64cb9f36
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_64cb9f36

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V,
      N.edgeSet ⊂ P.edgeSet → ¬ WilliamsonShmoys.HasPlanarDrawingOn P) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨P, hNP, hP, hPmax⟩ :=
    WilliamsonShmoys.exists_maximal_extension_for_edge_count_64cb9f36 N hN
  have hPc := WilliamsonShmoys.maximal_planar_drawing_edge_count_64cb9f36
    P hP hV hPmax
  have hEq : N.edgeSet = P.edgeSet := by
    by_contra hne
    have hStrict : N.edgeSet ⊂ P.edgeSet := by
      refine ⟨hNP, ?_⟩
      intro hPN
      apply hne
      exact Set.Subset.antisymm hNP hPN
    exact hmax P hStrict hP
  rw [hEq]
  exact hPc