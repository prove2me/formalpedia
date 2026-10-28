-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_graph_has_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:47:24.114176+00:00
-- url     : https://prove2.me/submissions/27bcc7cc-e3e3-4bb0-8ff5-8708b21bb96e

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
    ∃ R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      S ≤ R ∧
      ∀ T : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn T →
        R ≤ T → T = R := by
  obtain ⟨R, h1, h2, h3⟩ := S216WS.exists_maximal S _ hS
  exact ⟨R, h2, h1, fun T hT hRT => h3 T hRT hT⟩
