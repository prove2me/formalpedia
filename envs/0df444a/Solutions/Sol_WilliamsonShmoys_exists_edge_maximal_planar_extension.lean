-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:26:40.445453+00:00
-- url     : https://prove2.me/submissions/2034610f-7afb-47dc-9fc2-5ed8faf27c18

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite_property
import Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_supergraph_of_finite_property
      (P := WilliamsonShmoys.HasPlanarDrawingOn)
      (hdown := fun {G H} hGH hH =>
        WilliamsonShmoys.hasPlanarDrawingOn_mono hGH hH)
      K hK
  exact ⟨L, hKL, hL, hmax⟩