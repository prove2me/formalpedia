-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_extension__p2m_3bd27e40_28f0_4f6f_8869_04bf87b1e140_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:01:40.699904+00:00
-- url     : https://prove2.me/submissions/a905f2f1-9fd1-4fe8-b85e-7897f2d88eda

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_9ca2ebd3_f99a_4019_8342_a41927f598bc_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_9ca2ebd3_f99a_4019_8342_a41927f598bc_a4

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    Exists (fun K : SimpleGraph V => Exists (fun dK : DecidableRel K.Adj =>
      HasPlanarDrawingOn K /\
      (letI : DecidableRel K.Adj := dK
       H.edgeFinset ⊆ K.edgeFinset /\
       K.edgeFinset.card = 3 * Fintype.card V - 6))) := by
  obtain ⟨K, dK, hK, hmax, hsub⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_9ca2ebd3_f99a_4019_8342_a41927f598bc_a3
      H hH
  letI : DecidableRel K.Adj := dK
  refine ⟨K, dK, hK, hsub, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_9ca2ebd3_f99a_4019_8342_a41927f598bc_a4
    K hK hmax hV