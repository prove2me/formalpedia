-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_f4d7c237_0776_4adb_8bad_5150d3e32462_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:06:03.330343+00:00
-- url     : https://prove2.me/submissions/8a878457-e8b8-4be6-847c-691bec8554ab

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet = H.edgeSet) := by
  classical
  let S : Set (SimpleGraph V) :=
    {K | G.edgeSet ⊆ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K}
  have hSfin : S.Finite :=
    Set.Finite.subset Set.finite_univ (by
      intro K hK
      trivial)
  have hSne : S.Nonempty := ⟨G, Set.Subset.rfl, hG⟩
  obtain ⟨H, hH, hmax⟩ := hSfin.exists_maximal hSne
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro K hHK hK
  have hKmem : K ∈ S := ⟨hH.1.trans hHK, hK⟩
  have hHKle : H ≤ K := SimpleGraph.edgeSet_subset_edgeSet.mp hHK
  have hKHle : K ≤ H := hmax hKmem hHKle
  have hEq : H = K := le_antisymm hHKle hKHle
  simpa [hEq]