-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_e26f4eeb_ea90_4bc7_9f3f_02f85b28272b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:07:05.808655+00:00
-- url     : https://prove2.me/submissions/611fbc2d-79a1-4d0e-9b31-d747f7039678

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_maximal_extension__p2m_8963bb62_e14c_4266_badc_3102e502f664_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_8963bb62_e14c_4266_badc_3102e502f664_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    Exists fun H : SimpleGraph V => Exists fun dH : DecidableRel H.Adj =>
      HasPlanarDrawingOn H /\
      (forall u v, K.Adj u v -> H.Adj u v) /\
      K.edgeFinset.card <= (by letI : DecidableRel H.Adj := dH; exact H.edgeFinset.card) /\
      (by letI : DecidableRel H.Adj := dH; exact H.edgeFinset.card) = 3 * Fintype.card V - 6 := by
  obtain ⟨H, dH, hH, hKH, hCard, hMax⟩ :=
    WilliamsonShmoys.planarDrawing_maximal_extension__p2m_8963bb62_e14c_4266_badc_3102e502f664_a1
      K hK
  letI : DecidableRel H.Adj := dH
  have hExact :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_8963bb62_e14c_4266_badc_3102e502f664_a1
      H hH hV hMax
  exact ⟨H, dH, hH, hKH, hCard, hExact⟩