-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_578e1ae6_405d_472f_8260_c63e86041167_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:46:02.67142+00:00
-- url     : https://prove2.me/submissions/a0cd4bd8-07c5-444a-ba10-c216dff8b974

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_with_few_edges_has_proper_drawable_extension__p2m_cec667e7_b432_426e_9cef_b901d387a12d_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) [DecidableRel L.Adj],
      (∀ {u v}, K.Adj u v → L.Adj u v) →
      HasPlanarDrawingOn L →
      ∀ {u v}, L.Adj u v → K.Adj u v) :
    3 * Fintype.card V - 6 ≤ K.edgeFinset.card := by
  by_contra hbound
  have hE : K.edgeFinset.card < 3 * Fintype.card V - 6 := by omega
  obtain ⟨L, hLdec, hsub, hnew, hL⟩ :=
    WilliamsonShmoys.drawable_graph_with_few_edges_has_proper_drawable_extension__p2m_cec667e7_b432_426e_9cef_b901d387a12d_a1
      K hK hV hE
  letI : DecidableRel L.Adj := hLdec
  have hLK : ∀ {u v : V}, L.Adj u v → K.Adj u v := by
    intro u v hLuv
    exact hmax L (fun {u v : V} (hKuv : K.Adj u v) =>
      hsub (u := u) (v := v) hKuv) hL hLuv
  obtain ⟨u, v, hLuv, hnotKuv⟩ := hnew
  exact hnotKuv (hLK hLuv)