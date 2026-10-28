-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph_of_component_edge_steps_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:20:46.215603+00:00
-- url     : https://prove2.me/submissions/eb745b7f-fc87-4395-858b-fb54f3f01bf2

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

open WilliamsonShmoys in
theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G) (hV : 0 < Fintype.card V) (hstep : ∀ G : SimpleGraph V, HasPlanarDrawingOn G → ¬ G.Connected → ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v) : ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  obtain ⟨H, hGH, hP, hmax⟩ := S216WS.exists_maximal G _ hdraw
  refine ⟨H, hGH, ?_, hP⟩
  by_contra hc
  obtain ⟨K, hHK, hPK, u, v, hnr, hadj⟩ := hstep H hP hc
  have hKH := hmax K hHK hPK
  rw [hKH] at hadj
  exact hnr hadj.reachable
