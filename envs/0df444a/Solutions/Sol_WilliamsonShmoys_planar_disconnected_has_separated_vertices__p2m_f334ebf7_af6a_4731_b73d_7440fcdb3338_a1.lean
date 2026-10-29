-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_has_separated_vertices__p2m_f334ebf7_af6a_4731_b73d_7440fcdb3338_a1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:23:03.738737+00:00
-- url     : https://prove2.me/submissions/f129659f-1507-4e45-819e-152d59bc6d72

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 2 ≤ Fintype.card V)
    (hNot : ¬ K.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ K.Adj u v ∧ ¬ K.Reachable u v := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hpre : ¬ K.Preconnected := fun h => hNot ((SimpleGraph.connected_iff K).mpr ⟨h, hne⟩)
  simp only [SimpleGraph.Preconnected, not_forall] at hpre
  obtain ⟨u, v, h⟩ := hpre
  refine ⟨u, v, ?_, fun a => h a.reachable, h⟩
  intro e
  subst e
  exact h (SimpleGraph.Reachable.refl _)
