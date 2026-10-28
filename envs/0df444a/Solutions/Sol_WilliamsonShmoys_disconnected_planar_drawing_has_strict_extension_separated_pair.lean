-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_drawing_has_strict_extension_separated_pair
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T11:35:46.231531+00:00
-- url     : https://prove2.me/submissions/b69cf1a4-9af2-481a-9cce-aec14bce0cfa

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
namespace WilliamsonShmoys
theorem _root_.solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ G.Reachable u v := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hp : ¬ G.Preconnected := fun h => hDisconnected ⟨h⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hp
  obtain ⟨u, v, huv⟩ := hp
  exact ⟨u, v, fun h => huv (h ▸ SimpleGraph.Reachable.refl u), huv⟩
end WilliamsonShmoys

