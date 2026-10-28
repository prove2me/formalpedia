-- Prove2me | solution 1 for WilliamsonShmoys.finite_connected_supergraph_from_one_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:03:29.293589+00:00
-- url     : https://prove2.me/submissions/fbc374bd-79c7-40bf-b829-a4b652bf23bc

import Mathlib

namespace S216WS

/-- In a finite vertex type, any property with a witness above `W` has a maximal witness
(w.r.t. `≤`) above `W`. -/
lemma exists_maximal {V : Type} [Fintype V] (W : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P W) : ∃ H : SimpleGraph V, W ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  obtain ⟨H, ⟨hWH, hPH⟩, hmax⟩ := Set.Finite.exists_maximal
    (s := {G : SimpleGraph V | W ≤ G ∧ P G}) (Set.toFinite _) ⟨W, le_rfl, hP⟩
  exact ⟨H, hWH, hPH, fun K hHK hPK => le_antisymm (hmax ⟨le_trans hWH hHK, hPK⟩ hHK) hHK⟩

end S216WS

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P W)
    (hStep : ∀ G : SimpleGraph V, W ≤ G → P G → ¬ G.Connected →
      ∃ K : SimpleGraph V, G ≤ K ∧ G ≠ K ∧ P K) :
    ∃ H : SimpleGraph V, W ≤ H ∧ H.Connected ∧ P H := by
  obtain ⟨H, hWH, hPH, hmax⟩ := S216WS.exists_maximal W P hP
  refine ⟨H, hWH, ?_, hPH⟩
  by_contra hc
  obtain ⟨K, hHK, hne, hPK⟩ := hStep H hWH hPH hc
  exact hne (hmax K hHK hPK).symm
