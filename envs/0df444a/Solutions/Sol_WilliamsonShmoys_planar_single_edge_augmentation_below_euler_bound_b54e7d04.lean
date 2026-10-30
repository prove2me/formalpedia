-- Prove2me | solution 1 for WilliamsonShmoys.planar_single_edge_augmentation_below_euler_bound_b54e7d04
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:42:30.397125+00:00
-- url     : https://prove2.me/submissions/9eed4847-766f-49db-bfcb-450f4c3317b6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_b54e7d04
import Theorems.Thm_WilliamsonShmoys_extract_single_edge_from_planar_extension_b54e7d04

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hsmall : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊂ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = G.edgeSet.ncard + 1 := by
  obtain ⟨K, hGK, hKplanar, hKcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion_b54e7d04 G hV hG
  exact WilliamsonShmoys.extract_single_edge_from_planar_extension_b54e7d04
    G K hGK hKplanar hsmall hKcount
