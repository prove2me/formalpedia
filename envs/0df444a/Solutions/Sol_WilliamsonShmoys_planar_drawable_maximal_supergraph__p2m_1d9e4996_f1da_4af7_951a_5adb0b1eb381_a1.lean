-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_maximal_supergraph__p2m_1d9e4996_f1da_4af7_951a_5adb0b1eb381_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:34:34.339677+00:00
-- url     : https://prove2.me/submissions/94b8e913-f9bf-4123-859f-d9a4b7e72747

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_monotone_under_edge_subset__p2m_d8aa7015_594b_44f0_b66b_a7cd4c31cad4_a1
import Theorems.Thm_WilliamsonShmoys_finite_hereditary_maximal_supergraph__p2m_d8aa7015_594b_44f0_b66b_a7cd4c31cad4_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) : ∃ P : SimpleGraph V, Set.Subset N.edgeSet P.edgeSet ∧ HasPlanarDrawingOn P ∧ ∀ Q : SimpleGraph V, Set.Subset P.edgeSet Q.edgeSet → HasPlanarDrawingOn Q → Set.Subset Q.edgeSet P.edgeSet := by
  exact WilliamsonShmoys.finite_hereditary_maximal_supergraph__p2m_d8aa7015_594b_44f0_b66b_a7cd4c31cad4_a1
    HasPlanarDrawingOn
    (fun hQP hQ => WilliamsonShmoys.planar_drawing_monotone_under_edge_subset__p2m_d8aa7015_594b_44f0_b66b_a7cd4c31cad4_a1 hQP hQ)
    N hN