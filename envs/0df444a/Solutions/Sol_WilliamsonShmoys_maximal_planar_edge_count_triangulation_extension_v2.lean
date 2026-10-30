-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_triangulation_extension_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:03:59.66992+00:00
-- url     : https://prove2.me/submissions/a7514742-9712-41fb-af12-30fd632a7908

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_by_edge_max_e86e41b9
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_face_equations_e86e41b9

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    exists L : SimpleGraph V,
      K <= L /\ HasPlanarDrawingOn L /\
        L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.maximal_drawable_extension_by_edge_max_e86e41b9 K hK
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_drawable_face_equations_e86e41b9 L hL hMax hCard
  have hCount : L.edgeSet.ncard + 6 = 3 * Fintype.card V := by omega
  exact ⟨L, hKL, hL, hCount⟩