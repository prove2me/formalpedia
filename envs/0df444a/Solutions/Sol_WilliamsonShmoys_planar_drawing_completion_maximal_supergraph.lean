-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:38:03.095414+00:00
-- url     : https://prove2.me/submissions/2d0a3b98-4b20-4468-8e6e-6237b41121c8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_hereditary_property
import Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_of_le

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V,
      LE.le U W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
        (∀ X : SimpleGraph V, LE.le W X → WilliamsonShmoys.HasPlanarDrawingOn X → LE.le X W) := by
  obtain ⟨W, hUW, hW, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_supergraph_for_hereditary_property
      (P := WilliamsonShmoys.HasPlanarDrawingOn)
      (hher := by
        intro G H hGH hH
        exact WilliamsonShmoys.hasPlanarDrawingOn_of_le hGH hH)
      U hU
  exact ⟨W, hUW, hW, hmax⟩