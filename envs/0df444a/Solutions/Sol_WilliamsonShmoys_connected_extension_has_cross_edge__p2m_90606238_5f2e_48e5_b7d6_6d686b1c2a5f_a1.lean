-- Prove2me | solution 1 for WilliamsonShmoys.connected_extension_has_cross_edge__p2m_90606238_5f2e_48e5_b7d6_6d686b1c2a5f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:24:20.139782+00:00
-- url     : https://prove2.me/submissions/d9e5d21b-3c2b-47e6-a5a4-28fd9c5cace9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V) (hKH : K ≤ H) (hHConnected : H.Connected)
    (hNotConnected : ¬ K.Connected)
    (hCross : ∀ x y : V, H.Adj x y → K.Adj x y ∨ ¬ K.Reachable x y) :
    ∃ u v : V, ¬ K.Reachable u v ∧ H.Adj u v := by
  by_contra hNoCross
  have hEdge : ∀ {u v : V}, H.Adj u v → K.Adj u v := by
    intro u v huv
    rcases hCross u v huv with hKuv | hNotReachable
    · exact hKuv
    · exact False.elim (hNoCross ⟨u, v, hNotReachable, huv⟩)
  have hPath : ∀ {u v : V}, H.Reachable u v → K.Reachable u v := by
    intro u v huv
    have hrel : Relation.ReflTransGen H.Adj u v :=
      (SimpleGraph.reachable_iff_reflTransGen u v).1 huv
    induction hrel with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail hprefix hadj ih =>
        have hprefixReach : H.Reachable _ _ :=
          (SimpleGraph.reachable_iff_reflTransGen _ _).2 hprefix
        exact (ih hprefixReach).trans (hEdge hadj).reachable
  letI : Nonempty V := hHConnected.nonempty
  apply hNotConnected
  refine SimpleGraph.Connected.mk ?_
  intro u v
  exact hPath (hHConnected.preconnected u v)