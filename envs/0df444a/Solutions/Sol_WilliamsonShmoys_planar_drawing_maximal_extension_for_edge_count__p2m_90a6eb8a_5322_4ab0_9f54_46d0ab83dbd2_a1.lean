-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count__p2m_90a6eb8a_5322_4ab0_9f54_46d0ab83dbd2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:01:18.429303+00:00
-- url     : https://prove2.me/submissions/f48cb18d-d6b3-4257-b708-846ab11a1079

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_strict_of_lt__p2m_4f8ddee9_6bbc_42a8_909b_77c7ff633307_a1
import Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_max_ncard__p2m_4f8ddee9_6bbc_42a8_909b_77c7ff633307_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M ≤ L := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_drawable_supergraph_max_ncard__p2m_4f8ddee9_6bbc_42a8_909b_77c7ff633307_a1
      K hK
  refine ⟨L, hKL, hL, ?_⟩
  intro M hLM hM
  by_contra hML
  have hlt : L < M :=
    lt_of_le_of_ne hLM (by
      intro hEq
      subst M
      exact hML le_rfl)
  exact (Nat.not_lt_of_ge (hmax M (hKL.trans hLM) hM))
    (WilliamsonShmoys.edgeSet_ncard_strict_of_lt__p2m_4f8ddee9_6bbc_42a8_909b_77c7ff633307_a1
      L M hlt)
