-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_ea362c92_0899_4173_a9a5_a6ca062e0269_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:03:33.232713+00:00
-- url     : https://prove2.me/submissions/4614b6eb-fc63-4598-b4cf-1975b86a8085

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

set_option autoImplicit false

open scoped Classical

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ L : SimpleGraph V,
      H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ K : SimpleGraph V, L ≤ K →
          WilliamsonShmoys.HasPlanarDrawingOn K → K = L := by
  classical
  let p : SimpleGraph V → Prop := fun G => H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hp : ∃ G : SimpleGraph V, p G := ⟨H, le_rfl, hH⟩
  obtain ⟨L, hDecL, hExt⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 hp
  letI : DecidableRel L.Adj := hDecL
  refine ⟨L, hExt.1.1, hExt.1.2, ?_⟩
  intro K hLK hK
  have hpK : p K := ⟨le_trans hExt.1.1 hLK, hK⟩
  exact ((SimpleGraph.IsExtremal.le_iff_eq hExt hpK).mp hLK).symm