-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension__p2m_3e96e4b7_ffaf_421c_b46f_8949f4d2645c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:22:16.080439+00:00
-- url     : https://prove2.me/submissions/2ca51d85-b756-467b-99ea-4a6114625450

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H := by
  classical
  let p : SimpleGraph V → Prop := fun G => K ≤ G ∧ HasPlanarDrawingOn G
  obtain ⟨H, _, hH⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 ⟨K, le_rfl, hK⟩
  refine ⟨H, hH.1.1, hH.1.2, ?_⟩
  intro J hHJ hJ
  have hJmax : J.edgeFinset.card ≤ H.edgeFinset.card := by
    apply hH.2
    exact ⟨hH.1.1.trans hHJ, hJ⟩
  have hEdges : H.edgeFinset = J.edgeFinset := by
    apply Finset.eq_of_subset_of_card_le
    · exact SimpleGraph.edgeFinset_subset_edgeFinset.mpr hHJ
    · exact hJmax
  have hGraph : H = J := SimpleGraph.edgeFinset_inj.mp hEdges
  exact hGraph.symm