-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_upper_bound__p2m_267a842e_101e_4cf6_b705_d11d92433d33_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:38:24.657591+00:00
-- url     : https://prove2.me/submissions/50412d06-bcaf-4d8e-a38f-b3810ecf610a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_e844fca5_030a_4b1e_8670_0e19dfc2fff4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound__p2m_e844fca5_030a_4b1e_8670_0e19dfc2fff4_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : 3 <= Fintype.card V) :
    (letI : DecidableRel H.Adj := dH;
     H.edgeFinset.card <= 3 * Fintype.card V - 6) := by
  let hExt :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_e844fca5_030a_4b1e_8670_0e19dfc2fff4_a1
      H dH hH
  let K : SimpleGraph V := Classical.choose hExt
  have hExtK :
      Exists fun dK : DecidableRel K.Adj =>
        H <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
          (forall L : SimpleGraph V, K <= L ->
            WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) /\
          (letI : DecidableRel H.Adj := dH;
           letI : DecidableRel K.Adj := dK;
           H.edgeFinset.card <= K.edgeFinset.card) :=
    Classical.choose_spec hExt
  let dK : DecidableRel K.Adj := Classical.choose hExtK
  have hprops := Classical.choose_spec hExtK
  have hHK := hprops.1
  have hK := hprops.2.1
  have hmax := hprops.2.2.1
  have hcards := hprops.2.2.2
  exact le_trans hcards
    (WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_e844fca5_030a_4b1e_8670_0e19dfc2fff4_a1
      K dK hK hmax hn)