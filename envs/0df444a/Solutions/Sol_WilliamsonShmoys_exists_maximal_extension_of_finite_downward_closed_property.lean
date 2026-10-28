-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_extension_of_finite_downward_closed_property
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:17:08.397713+00:00
-- url     : https://prove2.me/submissions/ab2a95cf-6345-491f-8bf3-c24808494b40

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
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V)
    (hK : P K)
    (hdown : ∀ ⦃G H : SimpleGraph V⦄, G ≤ H → P H → P G) :
    ∃ T : SimpleGraph V, K ≤ T ∧ P T ∧
      ∀ U : SimpleGraph V, T ≤ U → P U → U = T :=
  S216WS.exists_maximal K P hK
