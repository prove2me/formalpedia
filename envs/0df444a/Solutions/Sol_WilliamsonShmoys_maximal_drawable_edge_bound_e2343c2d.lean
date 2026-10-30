-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_bound_e2343c2d
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:36:12.509196+00:00
-- url     : https://prove2.me/submissions/c300b3c5-7f53-4dbe-8d19-3aa6aa7e6b60

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_extension_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → K ≠ N → ¬ HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by
  obtain ⟨K, hNK, hKdraw, hKcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulated_extension_edge_count N hdraw hV
  have hKN : K = N := by
    by_contra hne
    exact (hmax K hNK hne) hKdraw
  subst K
  omega