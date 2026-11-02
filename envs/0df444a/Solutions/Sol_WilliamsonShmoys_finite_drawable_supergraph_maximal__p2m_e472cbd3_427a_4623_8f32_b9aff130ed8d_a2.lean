-- Prove2me | solution 1 for WilliamsonShmoys.finite_drawable_supergraph_maximal__p2m_e472cbd3_427a_4623_8f32_b9aff130ed8d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:24:19.53778+00:00
-- url     : https://prove2.me/submissions/68d0351e-3139-44b8-9327-9d238b929a59

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hQ : HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V, Q ≤ R ∧ HasPlanarDrawingOn R ∧
      ∀ S : SimpleGraph V, R ≤ S → HasPlanarDrawingOn S → S = R := by
  classical
  obtain ⟨R, hRdec, hR⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists
      (p := fun G : SimpleGraph V => Q ≤ G ∧ HasPlanarDrawingOn G)).2
      ⟨Q, le_rfl, hQ⟩
  letI := hRdec
  refine ⟨R, hR.1.1, hR.1.2, ?_⟩
  intro S hRS hS
  have hPS : Q ≤ S ∧ HasPlanarDrawingOn S := ⟨le_trans hR.1.1 hRS, hS⟩
  have hEq : R = S :=
    (SimpleGraph.IsExtremal.le_iff_eq hR hPS).mp hRS
  exact hEq.symm