-- Prove2me | solution 2 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_92669c9b_dd39_4b0e_bff1_b3f1c8b950b1_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:53:46.142893+00:00
-- url     : https://prove2.me/submissions/0a24bc3e-fb3e-416c-a56a-2eee42abfb45

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


open WilliamsonShmoys in
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      Set.Subset M.edgeSet N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V,
        Set.Subset N.edgeSet P.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn P →
        Set.Subset P.edgeSet N.edgeSet := by
  obtain ⟨H,h1,h2,h3⟩ := S216WS.exists_maximal M _ hM
  exact ⟨H,SimpleGraph.edgeSet_mono h1,h2,fun P a b => by rw [h3 P (SimpleGraph.edgeSet_subset_edgeSet.mp a) b]; exact fun _ h => h⟩
