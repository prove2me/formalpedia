-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension__p2m_ed14ce5d_db85_45e0_baef_0034f9db9e54_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:53:51.197995+00:00
-- url     : https://prove2.me/submissions/26ec23f0-eb67-4054-b3a8-abfacdb74f69

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
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn W ∧ U ≤ W ∧
        ∀ X : SimpleGraph V,
          WilliamsonShmoys.HasPlanarDrawingOn X → W ≤ X → X ≤ W := by
  obtain ⟨H,h1,h2,h3⟩ := S216WS.exists_maximal U _ hU
  exact ⟨H,h2,h1,fun X a b => (h3 X b a).le⟩
