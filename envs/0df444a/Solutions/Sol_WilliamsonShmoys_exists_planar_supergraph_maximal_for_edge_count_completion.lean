-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_maximal_for_edge_count_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:06:53.868348+00:00
-- url     : https://prove2.me/submissions/f268e6c1-a9c2-4bae-aa0a-bfdc2db2a5df

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by
  classical
  let p : SimpleGraph V → Prop := fun G =>
    H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hp : ∃ G : SimpleGraph V, p G := ⟨H, le_rfl, hH⟩
  obtain ⟨K, dK, hK⟩ := (SimpleGraph.exists_isExtremal_iff_exists p).2 hp
  letI : DecidableRel K.Adj := dK
  refine ⟨K, hK.prop.1, hK.prop.2, ?_⟩
  intro L hKL hL
  have hKL' : K ≤ L := hKL
  have hEq : K = L := (hK.le_iff_eq ⟨hK.prop.1.trans hKL, hL⟩).mp hKL'
  exact hEq.symm.le