-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_has_nonadjacent_pair
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T11:10:47.953875+00:00
-- url     : https://prove2.me/submissions/810b256c-b926-45a3-9c9b-5e50f5c2b7ae

import Mathlib

set_option autoImplicit false
namespace WilliamsonShmoys
theorem _root_.solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdisc : ¬ Q.Connected) :
    ∃ u v, u ≠ v ∧ ¬ Q.Adj u v := by
  by_contra h
  push_neg at h
  apply hdisc
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have htop : Q = ⊤ := by
    ext u v; simp only [SimpleGraph.top_adj]; exact ⟨fun h' => h'.ne, h u v⟩
  subst htop; exact SimpleGraph.connected_top
end WilliamsonShmoys

