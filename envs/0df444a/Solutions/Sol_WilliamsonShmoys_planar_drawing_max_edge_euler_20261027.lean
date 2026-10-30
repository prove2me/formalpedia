-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_max_edge_euler_20261027
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:16:52.884024+00:00
-- url     : https://prove2.me/submissions/6d2974e7-066b-4750-93f4-c6770c8fb5ad

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_938af664_b2aa_4ceb_8ad4_a78c6b3943d3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet.ncard ≤ L.edgeSet.ncard) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hMcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_938af664_b2aa_4ceb_8ad4_a78c6b3943d3 L hV hL
  have hML : M.edgeSet.ncard ≤ L.edgeSet.ncard := hMax M hLM hM
  have hLupper :=
    WilliamsonShmoys.planar_edge_count_upper_bound_938af664_b2aa_4ceb_8ad4_a78c6b3943d3 L hV hL
  omega