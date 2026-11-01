-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_95f0e96c_588c_4293_a881_4eae330a335f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:42:15.146228+00:00
-- url     : https://prove2.me/submissions/b2223e0e-2dba-403a-bd21-deb7c3d96edd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_9df70f0c_e392_4539_bc07_082cd2cf5417_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V,
      L.edgeSet ⊆ T.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V,
        T.edgeSet ⊆ U.edgeSet →
        (∃ e, e ∈ U.edgeSet ∧ e ∉ T.edgeSet) →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn U := by
  classical
  obtain ⟨T, hLT, hT, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_extension__p2m_9df70f0c_e392_4539_bc07_082cd2cf5417_a1
      (P := WilliamsonShmoys.HasPlanarDrawingOn) hL
  refine ⟨T, (SimpleGraph.edgeSet_subset_edgeSet).2 hLT, hT, ?_⟩
  intro U hTU hnew hU
  obtain ⟨e, heU, heT⟩ := hnew
  have hTU' : T ≤ U := (SimpleGraph.edgeSet_subset_edgeSet).1 hTU
  have hUT' : U ≤ T := hmax U hTU' hU
  exact heT ((SimpleGraph.edgeSet_subset_edgeSet).2 hUT' heU)