-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_10381148_6b51_4b84_8aa4_8b409082ba4a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:43:59.702922+00:00
-- url     : https://prove2.me/submissions/7bb070fb-259c-4273-939f-2341b1f795dc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L = K := by
  classical
  let p : SimpleGraph V → Prop := fun K => G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K
  obtain ⟨K, hKDec, hK⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 ⟨G, le_rfl, hG⟩
  letI : DecidableRel K.Adj := hKDec
  refine ⟨K, (SimpleGraph.edgeSet_subset_edgeSet).2 hK.1.1, hK.1.2, ?_⟩
  intro L hKL hL
  have hKLle : K ≤ L := (SimpleGraph.edgeSet_subset_edgeSet).1 hKL
  have hGL : G ≤ L := le_trans hK.1.1 hKLle
  have hLp : p L := ⟨hGL, hL⟩
  exact ((SimpleGraph.IsExtremal.le_iff_eq hK hLp).mp hKLle).symm