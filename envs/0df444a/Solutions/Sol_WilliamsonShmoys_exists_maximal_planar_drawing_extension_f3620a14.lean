-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_drawing_extension_f3620a14
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:23:51.59227+00:00
-- url     : https://prove2.me/submissions/ab233b9f-3dae-4004-a250-1a8fca31bb64

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

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
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ S : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      T ≤ S ∧
      ∀ R : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn R → S ≤ R → R ≤ S := by
  obtain ⟨H, hTH, hP, hmax⟩ := S216WS.exists_maximal T _ hT
  exact ⟨H, hP, hTH, fun R hR hHR => (hmax R hHR hR).le⟩
