-- Prove2me | solution 1 for SimpleGraph.exists_adj_across_components_of_connected_supergraph__p2m_afb0646a_1b1c_43fc_91b8_89461203ac52_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:52:44.531203+00:00
-- url     : https://prove2.me/submissions/9e1e7ff8-8823-41a1-9260-1efaa546f486

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (G H : SimpleGraph V)
    (hSub : LE.le G H) (hHConnected : H.Connected) (hGNotConnected : Not G.Connected) :
    Exists fun u : V => Exists fun v : V => And (Not (G.Reachable u v)) (H.Adj u v) := by
  by_contra hNo
  have hStep : forall u v : V, H.Adj u v -> G.Reachable u v := by
    intro u v huv
    by_contra hNotReachable
    exact hNo (Exists.intro u (Exists.intro v (And.intro hNotReachable huv)))
  have hReach : forall u v : V, H.Reachable u v -> G.Reachable u v := by
    intro u v huv
    rw [H.reachable_iff_reflTransGen] at huv
    induction huv with
    | refl => exact SimpleGraph.Reachable.refl (G := G) _
    | tail _ ha hr => exact SimpleGraph.Reachable.trans hr (hStep _ _ ha)
  have hGConnected : G.Connected := by
    refine { preconnected := ?_, nonempty := hHConnected.nonempty }
    intro u v
    exact hReach u v (hHConnected u v)
  exact hGNotConnected hGConnected