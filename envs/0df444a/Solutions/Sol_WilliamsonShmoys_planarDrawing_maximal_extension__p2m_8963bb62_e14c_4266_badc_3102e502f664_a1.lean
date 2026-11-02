-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_maximal_extension__p2m_8963bb62_e14c_4266_badc_3102e502f664_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:50:52.879557+00:00
-- url     : https://prove2.me/submissions/2b74d7d8-d51a-45b1-a95e-3147bb452702

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_graph_property_maximal_supergraph__p2m_266b1a11_87af_4c8d_8cdc_f947960a0fd8_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K) :
    Exists fun H : SimpleGraph V => Exists fun dH : DecidableRel H.Adj =>
      And (HasPlanarDrawingOn H)
      (And (forall u v, K.Adj u v -> H.Adj u v)
      (And (K.edgeFinset.card <= (by letI : DecidableRel H.Adj := dH; exact H.edgeFinset.card))
      (forall J : SimpleGraph V, HasPlanarDrawingOn J ->
        (forall u v, H.Adj u v -> J.Adj u v) ->
        (forall u v, J.Adj u v -> H.Adj u v)))) := by
  exact finite_graph_property_maximal_supergraph__p2m_266b1a11_87af_4c8d_8cdc_f947960a0fd8_a1
    K HasPlanarDrawingOn hK
