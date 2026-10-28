-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph_9e31d0d7_bedf_4a6b_a6d6_c2c0226ce7c3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:41:07.43054+00:00
-- url     : https://prove2.me/submissions/7e368bb1-f057-4a45-8ae9-3426c1b38b5c

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
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S) :
    exists T : SimpleGraph V,
      (forall u v, S.Adj u v -> T.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn T /\
      S.edgeSet.ncard <= T.edgeSet.ncard /\
      (forall R : SimpleGraph V,
        (forall u v, T.Adj u v -> R.Adj u v) ->
        WilliamsonShmoys.HasPlanarDrawingOn R -> R = T) := by
  obtain ⟨T, h1, h2, h3⟩ := S216WS.exists_maximal S _ hS
  exact ⟨T, fun u v h => h1 h, h2,
    Set.ncard_le_ncard (SimpleGraph.edgeSet_mono h1) (Set.toFinite _),
    fun R hR hRd => h3 R (fun u v h => hR u v h) hRd⟩
