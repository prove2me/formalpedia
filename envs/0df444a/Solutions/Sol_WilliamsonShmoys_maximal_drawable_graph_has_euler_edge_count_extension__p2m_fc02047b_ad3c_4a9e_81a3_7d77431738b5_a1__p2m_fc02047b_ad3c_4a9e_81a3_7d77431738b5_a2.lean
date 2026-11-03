-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count_extension__p2m_fc02047b_ad3c_4a9e_81a3_7d77431738b5_a1__p2m_fc02047b_ad3c_4a9e_81a3_7d77431738b5_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:24:26.924513+00:00
-- url     : https://prove2.me/submissions/daee69c0-190d-4b5b-9222-2f11ad148d6d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_c985394f_ff9a_4827_826c_d7a45e5d518a_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count__p2m_c985394f_ff9a_4827_826c_d7a45e5d518a_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hdraw : HasPlanarDrawingOn G) :
    letI : forall H : SimpleGraph V, DecidableRel H.Adj := fun H => Classical.decRel H.Adj
    exists N : SimpleGraph V,
      (forall u v, G.Adj u v -> N.Adj u v) /\
      HasPlanarDrawingOn N /\
      3 * Fintype.card V - 6 = N.edgeFinset.card := by
  classical
  letI : forall H : SimpleGraph V, DecidableRel H.Adj := fun H => Classical.decRel H.Adj
  let hExt :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_c985394f_ff9a_4827_826c_d7a45e5d518a_a1
      G hdraw
  let N : SimpleGraph V := Classical.choose hExt
  have hGN : forall u v, G.Adj u v -> N.Adj u v := (Classical.choose_spec hExt).1
  have hNdraw : HasPlanarDrawingOn N := (Classical.choose_spec hExt).2.1
  have hmax : forall H : SimpleGraph V,
      (forall u v, N.Adj u v -> H.Adj u v) -> HasPlanarDrawingOn H -> H = N :=
    (Classical.choose_spec hExt).2.2
  have hcount :=
    WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count__p2m_c985394f_ff9a_4827_826c_d7a45e5d518a_a2
      N hcard hNdraw hmax
  refine Exists.intro N ?_
  refine And.intro hGN ?_
  refine And.intro hNdraw hcount