-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_for_maximal_drawable
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:17:15.149013+00:00
-- url     : https://prove2.me/submissions/9460228a-99a7-4f12-b332-f2809372235a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_finite_drawable_supergraph_maximal_by_inclusion
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_face_counting_equations

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hV : 3 ≤ Fintype.card V)
    (hgap : T.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧ U ≠ T ∧ WilliamsonShmoys.HasPlanarDrawingOn U := by
  obtain ⟨M, hTM, hM, hMax⟩ :=
    WilliamsonShmoys.exists_finite_drawable_supergraph_maximal_by_inclusion T hT
  by_cases hEq : M = T
  · subst M
    obtain ⟨f, hEuler, hIncidence⟩ :=
      WilliamsonShmoys.maximal_drawable_face_counting_equations T hT hMax hV
    omega
  · exact ⟨M, hTM, hEq, hM⟩