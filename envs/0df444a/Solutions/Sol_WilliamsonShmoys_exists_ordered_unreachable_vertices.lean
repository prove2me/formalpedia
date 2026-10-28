-- Prove2me | solution 1 for WilliamsonShmoys.exists_ordered_unreachable_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:46:34.84899+00:00
-- url     : https://prove2.me/submissions/9eedccb5-26ca-41b3-8cdb-b94bdf51980f

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hGdisc : ¬ G.Connected) :
    ∃ u v : V, u < v ∧ ¬ G.Reachable u v := by
  by_contra hbad
  apply hGdisc
  refine { preconnected := ?_, nonempty := ?_ }
  · intro u v
    by_contra hnot
    have hne : u ≠ v := by
      intro huv
      subst v
      exact hnot (SimpleGraph.Reachable.refl u)
    rcases lt_or_gt_of_ne hne with huv | hvu
    · exact False.elim (hbad ⟨u, v, huv, hnot⟩)
    · exact False.elim (hbad ⟨v, u, hvu, fun h => hnot (SimpleGraph.Reachable.symm h)⟩)
  · exact Fintype.card_pos_iff.mp (by omega)