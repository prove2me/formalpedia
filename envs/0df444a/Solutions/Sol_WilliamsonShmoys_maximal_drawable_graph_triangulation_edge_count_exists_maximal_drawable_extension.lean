-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_triangulation_edge_count_exists_maximal_drawable_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:58:34.008825+00:00
-- url     : https://prove2.me/submissions/4e189406-4e23-469e-8bf2-8132fb2a143d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_finite_downward_closed_property

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ T : SimpleGraph V, K ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T := by
  obtain ⟨T, hKT, hT, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_extension_of_finite_downward_closed_property
      WilliamsonShmoys.HasPlanarDrawingOn K hK (by
        intro G H hGH hH
        rcases hH with ⟨p, arc, hpinj, hedge, hcross⟩
        refine ⟨p, arc, hpinj, ?_, ?_⟩
        · intro u v huv hGuv
          exact hedge u v huv (hGH hGuv)
        · intro u v x y huv hxy hGuv hGxy hne
          exact hcross u v x y huv hxy (hGH hGuv) (hGH hGxy) hne)
  exact ⟨T, hKT, hT, hmax⟩