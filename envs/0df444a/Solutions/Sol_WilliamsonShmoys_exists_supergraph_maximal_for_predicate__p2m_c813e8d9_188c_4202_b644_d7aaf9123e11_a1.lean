-- Prove2me | solution 1 for WilliamsonShmoys.exists_supergraph_maximal_for_predicate__p2m_c813e8d9_188c_4202_b644_d7aaf9123e11_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:59:26.000008+00:00
-- url     : https://prove2.me/submissions/52541977-8671-4866-b387-2664f3196ff1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

namespace S216WS

lemma exists_maximal {V : Type} [Fintype V] (W : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P W) : ∃ H : SimpleGraph V, W ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  obtain ⟨H, ⟨hWH, hPH⟩, hmax⟩ := Set.Finite.exists_maximal
    (s := {G : SimpleGraph V | W ≤ G ∧ P G}) (Set.toFinite _) ⟨W, le_rfl, hP⟩
  exact ⟨H, hWH, hPH, fun K hHK hPK => le_antisymm (hmax ⟨le_trans hWH hHK, hPK⟩ hHK) hHK⟩

end S216WS


open WilliamsonShmoys in
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hM : P M) :
    ∃ N : SimpleGraph V,
      Set.Subset M.edgeSet N.edgeSet ∧
      P N ∧
      ∀ Q : SimpleGraph V,
        Set.Subset N.edgeSet Q.edgeSet →
        P Q →
        Set.Subset Q.edgeSet N.edgeSet := by
  obtain ⟨H,h1,h2,h3⟩ := S216WS.exists_maximal M _ hM
  exact ⟨H,SimpleGraph.edgeSet_mono h1,h2,fun Q a b => by rw [h3 Q (SimpleGraph.edgeSet_subset_edgeSet.mp a) b]; exact fun _ h => h⟩
