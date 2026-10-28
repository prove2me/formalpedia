-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_of_augmentable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T04:19:04.108972+00:00
-- url     : https://prove2.me/submissions/b20e0d3c-2c68-466c-bde1-5256f0fdc79e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hAugment :
      ∀ X : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn X →
        ¬ X.Connected →
        ∃ Z : SimpleGraph V,
          X ≤ Z ∧
          X.edgeSet.ncard < Z.edgeSet.ncard ∧
          WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ Z : SimpleGraph V,
      Y ≤ Z ∧
      Y.edgeSet.ncard ≤ Z.edgeSet.ncard ∧
      Z.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z := by
  classical
  obtain ⟨P, hPm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => Y ≤ H ∧ HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeSet.ncard) ⟨Y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hY⟩⟩
  obtain ⟨hYP, hP⟩ : Y ≤ P ∧ HasPlanarDrawingOn P := (Finset.mem_filter.mp hPm).2
  refine ⟨P, hYP, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hYP) (Set.toFinite _), ?_, hP⟩
  by_contra hc
  obtain ⟨Z, hPZ, hlt, hZ⟩ := hAugment P hP hc
  have := hmax Z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hYP.trans hPZ, hZ⟩)
  omega
