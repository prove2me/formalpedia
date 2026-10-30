-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_augmentable_below_maximal_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:03:17.475999+00:00
-- url     : https://prove2.me/submissions/20e2c21c-1fe4-4f6d-8baf-1b04bad466ab

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_extension_eeac03ef_36e6_44d1_be88_71ee042c1f55
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count_eeac03ef_36e6_44d1_be88_71ee042c1f55

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hsparse : K.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ L : SimpleGraph V,
      K <= L ∧ K ≠ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by
  obtain ⟨L, hKL, hdraw, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_drawable_extension_eeac03ef_36e6_44d1_be88_71ee042c1f55 K hK
  have hcard :=
    WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count_eeac03ef_36e6_44d1_be88_71ee042c1f55 L hV hdraw hmax
  refine ⟨L, hKL, ?_, hdraw⟩
  intro hEq
  subst L
  omega