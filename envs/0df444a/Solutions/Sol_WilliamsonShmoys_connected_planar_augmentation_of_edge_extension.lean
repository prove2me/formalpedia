-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_augmentation_of_edge_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:20:53.198273+00:00
-- url     : https://prove2.me/submissions/b26e5d17-43a0-40d8-a989-27f30ecd41a9

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
theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : HasPlanarDrawingOn K) (hInsert : forall (G : SimpleGraph V), 3 <= Fintype.card V -> HasPlanarDrawingOn G -> ¬ G.Connected -> Exists fun H : SimpleGraph V => (Exists fun u : V => Exists fun v : V => u ≠ v ∧ ¬ G.Reachable u v ∧ (forall x y : V, H.Adj x y ↔ G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u))) ∧ HasPlanarDrawingOn H) : Exists fun H : SimpleGraph V => (forall u v : V, K.Adj u v -> H.Adj u v) ∧ K.edgeSet.ncard <= H.edgeSet.ncard ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  obtain ⟨H, hKH, hP, hmax⟩ := S216WS.exists_maximal K _ hK
  refine ⟨H, fun u v h => hKH h, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hKH) (Set.toFinite _), ?_, hP⟩
  by_contra hc
  obtain ⟨H', ⟨u, v, _, hnr, hadj⟩, hP'⟩ := hInsert H hV hP hc
  have hle : H ≤ H' := fun x y h => (hadj x y).2 (Or.inl h)
  have hH' := hmax H' hle hP'
  have : H'.Adj u v := (hadj u v).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
  rw [hH'] at this
  exact hnr this.reachable
