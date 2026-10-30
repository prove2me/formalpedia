-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_9cc0c9d9_a289_45c0_90c4_3b812fbd190b_a1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T19:02:41.992389+00:00
-- url     : https://prove2.me/submissions/f071594b-aee0-416a-8dd5-adff3a1e0c14

import Mathlib.Order.Preorder.Finite
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      Set.Subset G.edgeSet M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        Set.Subset M.edgeSet N.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by
  classical
  -- Use Finite.exists_le_maximal with the predicate HasPlanarDrawingOn
  obtain ⟨M, hGM, hmax⟩ := Finite.exists_le_maximal (p := fun H : SimpleGraph V => WilliamsonShmoys.HasPlanarDrawingOn H) hG
  
  refine' ⟨M, _, hmax.prop, _⟩
  · -- Prove Set.Subset G.edgeSet M.edgeSet
    -- Convert graph order to edge set subset using SimpleGraph.edgeSet_subset_edgeSet
    exact SimpleGraph.edgeSet_subset_edgeSet.mpr hGM
  · -- Prove maximality: ∀ N : SimpleGraph V, Set.Subset M.edgeSet N.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn N → N = M
    intro N hMN hN
    -- Convert edge set subset to graph order
    have hMN' : M ≤ N := by
      exact SimpleGraph.edgeSet_subset_edgeSet.mp hMN
    -- Use maximality to get N ≤ M
    have hNM : N ≤ M := hmax.le_of_ge hN hMN'
    -- Apply antisymmetry to get N = M
    exact le_antisymm hNM hMN'