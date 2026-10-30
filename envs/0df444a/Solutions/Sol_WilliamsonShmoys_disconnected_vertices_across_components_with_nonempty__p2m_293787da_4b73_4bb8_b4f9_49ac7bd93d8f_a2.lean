-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_vertices_across_components_with_nonempty__p2m_293787da_4b73_4bb8_b4f9_49ac7bd93d8f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:37:26.247237+00:00
-- url     : https://prove2.me/submissions/b860996b-1ea3-4551-b17e-57da06187d5a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdis : ¬ G.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ G.Reachable u v := by
  have hcard : 0 < Fintype.card V := by omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp hcard
  by_contra h
  apply hdis
  refine ⟨?_⟩
  intro u v
  by_contra huv
  have hne : u ≠ v := by
    intro heq
    subst v
    exact huv (SimpleGraph.Reachable.refl (G := G) u)
  exact h ⟨u, v, hne, huv⟩