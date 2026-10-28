-- Prove2me | solution 1 for WilliamsonShmoys.exists_separated_nonadjacent_vertices
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:54:37.171699+00:00
-- url     : https://prove2.me/submissions/f2129b4c-5c86-460f-924f-165982bec50b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ H.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ H.Adj u v ∧ ¬ H.Reachable u v := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hpre : ¬ H.Preconnected := fun h => hNotConnected ⟨h⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hpre
  obtain ⟨u, v, h⟩ := hpre
  refine ⟨u, v, ?_, fun ha => h ha.reachable, h⟩
  rintro rfl; exact h (SimpleGraph.Reachable.refl u)
