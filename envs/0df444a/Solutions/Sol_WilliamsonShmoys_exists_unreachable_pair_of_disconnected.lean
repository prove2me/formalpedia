-- Prove2me | solution 1 for WilliamsonShmoys.exists_unreachable_pair_of_disconnected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T12:06:51.499171+00:00
-- url     : https://prove2.me/submissions/cd291517-eec1-4c81-a06b-3be114f9511d

import Mathlib

set_option autoImplicit false
namespace WilliamsonShmoys
theorem _root_.solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hNonempty : 0 < Fintype.card V)
    (hNotConnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp hNonempty
  have hp : ¬ G.Preconnected := fun h => hNotConnected ⟨h⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hp
  exact hp
end WilliamsonShmoys

