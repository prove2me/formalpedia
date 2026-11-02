-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_3a1649bb_b908_4400_8c80_435b14739a2c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:02:06.160232+00:00
-- url     : https://prove2.me/submissions/c2e632dd-af3d-44f8-b76b-bb0615ee041b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ M : SimpleGraph V,
      H.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ L : SimpleGraph V,
        M.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        M.edgeSet = L.edgeSet := by
  classical
  let p : SimpleGraph V → Prop := fun G => H.edgeSet ⊆ G.edgeSet ∧
    WilliamsonShmoys.HasPlanarDrawingOn G
  have hp : ∃ G : SimpleGraph V, p G := by
    exact ⟨H, Set.Subset.rfl, hH⟩
  obtain ⟨M, hdecM, hM⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 hp
  letI : DecidableRel M.Adj := hdecM
  rcases hM with ⟨hMp, hmax⟩
  rcases hMp with ⟨hHM, hMdraw⟩
  refine ⟨M, hHM, hMdraw, ?_⟩
  intro L hML hLdraw
  have hML' : M ≤ L := SimpleGraph.edgeSet_subset_edgeSet.mp hML
  have hLp : p L := ⟨Set.Subset.trans hHM hML, hLdraw⟩
  have hEq : M = L := (SimpleGraph.IsExtremal.le_iff_eq ⟨⟨hHM, hMdraw⟩, hmax⟩ hLp).mp hML'
  exact hEq ▸ rfl
