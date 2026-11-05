-- Prove2me | solution 1 for WilliamsonShmoys.iterate_planar_extensions_for_pairs__p2m_1f4c177d_eb20_4750_9a13_0c928226c3d6_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T20:28:15.799853+00:00
-- url     : https://prove2.me/submissions/e913168e-aada-4573-9112-07b1921bd562

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hstep : ∀ (G : SimpleGraph V), HasPlanarDrawingOn G →
      ∀ u v : V, ¬ G.Reachable u v →
        ∃ K : SimpleGraph V,
          HasPlanarDrawingOn K ∧ G ≤ K ∧ K.Adj u v)
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (pairs : List (V × V)) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧ G ≤ H ∧ ∀ p ∈ pairs, H.Reachable p.1 p.2 := by
  induction pairs with
  | nil =>
      exact ⟨G, hG, le_rfl, by simp⟩
  | cons p ps ih =>
      obtain ⟨H0, hH0, hGH0, hreach0⟩ := ih
      by_cases hp : H0.Reachable p.1 p.2
      · refine ⟨H0, hH0, hGH0, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact hp
        · exact hreach0 q hq'
      · obtain ⟨K, hK, hH0K, hadj⟩ := hstep H0 hH0 p.1 p.2 hp
        refine ⟨K, hK, hGH0.trans hH0K, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact hadj.reachable
        · exact SimpleGraph.Reachable.mono hH0K (hreach0 q hq')
