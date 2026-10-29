-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_f480263f_1ac3_4297_8888_36232c8b7a10_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:53:49.9247+00:00
-- url     : https://prove2.me/submissions/d9293d92-1419-4307-b7a5-2631e4ea3ae9

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
    exists K : SimpleGraph V,
      M <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
        (forall L : SimpleGraph V, K <= L ->
          WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) := S216WS.exists_maximal M _ hM
