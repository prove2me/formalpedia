-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_finite_edge_count_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:42:04.027458+00:00
-- url     : https://prove2.me/submissions/4cd86ed6-2969-47fa-b608-d27dd202c9a9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_max_edge_count_planar_supergraph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet ⊆ H.edgeSet ∧
      (∀ J : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn J →
        H.edgeSet ⊆ J.edgeSet → J.edgeSet ⊆ H.edgeSet) := by
  obtain ⟨H, hH, hKH, hmax⟩ :=
    WilliamsonShmoys.exists_max_edge_count_planar_supergraph K hK
  refine ⟨H, hH, hKH, ?_⟩
  intro J hJ hHJ
  intro e heJ
  by_contra heH
  have hproper : H.edgeSet ⊂ J.edgeSet := by
    refine ⟨hHJ, ?_⟩
    intro hJH
    exact heH (hJH heJ)
  have hlt : H.edgeSet.ncard < J.edgeSet.ncard :=
    Set.ncard_lt_ncard hproper
  exact (not_lt_of_ge (hmax J hJ hHJ)) hlt
