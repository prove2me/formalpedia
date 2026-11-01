-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_9fcd878d_5db4_4b13_99bb_56edaa5c5ac0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:08:22.291528+00:00
-- url     : https://prove2.me/submissions/d19d78c8-14db-4ad4-b3e0-9358afa27263

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ (P : SimpleGraph V),
        (∀ u v, N.Adj u v → P.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by
  classical
  let p : SimpleGraph V → Prop := fun G =>
    (∀ u v, M.Adj u v → G.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hp : ∃ G : SimpleGraph V, p G := by
    exact ⟨M, ⟨fun _ _ hadj => hadj, hM⟩⟩
  obtain ⟨N, dN, hN⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 hp
  letI : DecidableRel N.Adj := dN
  refine ⟨N, hN.1.1, hN.1.2, ?_⟩
  intro P hNP hP
  letI : DecidableRel P.Adj := Classical.decRel _
  have hpP : p P := by
    refine ⟨?_, hP⟩
    intro u v huv
    exact hNP u v (hN.1.1 u v huv)
  exact ((SimpleGraph.IsExtremal.le_iff_eq hN hpP).mp hNP).symm