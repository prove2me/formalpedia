-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_downward_closed
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:08:42.503905+00:00
-- url     : https://prove2.me/submissions/07b939ea-d059-4d3a-8e44-c5c0505d28b0

import Mathlib

namespace S216WS

lemma exists_maximal {V : Type} [Fintype V] (W : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P W) : ∃ H : SimpleGraph V, W ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  obtain ⟨H, ⟨hWH, hPH⟩, hmax⟩ := Set.Finite.exists_maximal
    (s := {G : SimpleGraph V | W ≤ G ∧ P G}) (Set.toFinite _) ⟨W, le_rfl, hP⟩
  exact ⟨H, hWH, hPH, fun K hHK hPK => le_antisymm (hmax ⟨le_trans hWH hHK, hPK⟩ hHK) hHK⟩

end S216WS

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ ⦃G H : SimpleGraph V⦄, G ≤ H → P H → P G)
    (G : SimpleGraph V) (hG : P G) :
    ∃ L : SimpleGraph V, G ≤ L ∧ P L ∧
      ∀ K : SimpleGraph V, L ≤ K → P K → K ≤ L := by
  obtain ⟨L, h1, h2, h3⟩ := S216WS.exists_maximal G P hG
  exact ⟨L, h1, h2, fun K hLK hK => (h3 K hLK hK).le⟩
