-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_property_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:49:58.927277+00:00
-- url     : https://prove2.me/submissions/9c2dc5c7-cc4c-43b7-b4be-e4a1f65dfcb1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

namespace S216WS

lemma exists_maximal {V : Type} [Fintype V] (W : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P W) : ∃ H : SimpleGraph V, W ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  obtain ⟨H, ⟨hWH, hPH⟩, hmax⟩ := Set.Finite.exists_maximal
    (s := {G : SimpleGraph V | W ≤ G ∧ P G}) (Set.toFinite _) ⟨W, le_rfl, hP⟩
  exact ⟨H, hWH, hPH, fun K hHK hPK => le_antisymm (hmax ⟨le_trans hWH hHK, hPK⟩ hHK) hHK⟩

end S216WS

theorem solution
    {V : Type} [Fintype V]
    (M : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hM : P M) :
    ∃ L : SimpleGraph V, M ≤ L ∧ P L ∧
      ∀ K : SimpleGraph V, L ≤ K → P K → K = L :=
  S216WS.exists_maximal M P hM
