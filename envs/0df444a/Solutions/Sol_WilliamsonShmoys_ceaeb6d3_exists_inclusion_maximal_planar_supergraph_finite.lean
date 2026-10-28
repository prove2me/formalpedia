-- Prove2me | solution 1 for WilliamsonShmoys.ceaeb6d3_exists_inclusion_maximal_planar_supergraph_finite
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:27:57.010285+00:00
-- url     : https://prove2.me/submissions/2261c5bd-e999-4799-a6e2-ce27ec56037b

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
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet ⊆ H.edgeSet) := by
  obtain ⟨H, hGH, hP, hmax⟩ := S216WS.exists_maximal G _ hG
  refine ⟨H, SimpleGraph.edgeSet_mono hGH, hP, fun K hHK hK => ?_⟩
  have hle : H ≤ K := SimpleGraph.edgeSet_subset_edgeSet.1 hHK
  rw [hmax K hle hK]
