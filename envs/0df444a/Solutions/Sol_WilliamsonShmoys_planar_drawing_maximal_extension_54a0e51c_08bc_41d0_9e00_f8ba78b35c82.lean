-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_54a0e51c_08bc_41d0_9e00_f8ba78b35c82
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:46:14.871204+00:00
-- url     : https://prove2.me/submissions/7a865ec8-0e47-4194-a118-6c2c010692e3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_drawable_maximum_cardinality

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        HasPlanarDrawingOn L →
        L.edgeSet ⊆ K.edgeSet := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.finite_drawable_maximum_cardinality H hH
  refine ⟨K, hHK, hK, ?_⟩
  intro L hKL hL
  by_contra hnot
  have hstrict : K.edgeSet ⊂ L.edgeSet := ⟨hKL, hnot⟩
  have hcard : K.edgeSet.ncard < L.edgeSet.ncard :=
    Set.ncard_lt_ncard hstrict
  have hHL : H.edgeSet ⊆ L.edgeSet := Set.Subset.trans hHK hKL
  have hmax' := hmax L hHL hL
  omega