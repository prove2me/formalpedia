-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_maximal_completion__p2m_aaf33811_225e_424c_a7fa_7688f68b512b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:39:50.177199+00:00
-- url     : https://prove2.me/submissions/20ad5bff-489b-4405-8747-aa3d5c5a6d68

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_partial_order_has_maximal_above__p2m_b857a82c_8bba_4f53_a10b_55c8fcca96a0_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  classical
  letI : Finite (SimpleGraph V) :=
    Finite.of_injective
      (fun G : SimpleGraph V => fun e : Sym2 V => decide (e ∈ G.edgeSet))
      (by
        intro G H h
        apply SimpleGraph.edgeSet_injective
        ext e
        have he := congrFun h e
        simpa using he)
  obtain ⟨L, hKL, hPL, hmax⟩ :=
    finite_partial_order_has_maximal_above__p2m_b857a82c_8bba_4f53_a10b_55c8fcca96a0_a1
      (α := SimpleGraph V)
      (P := fun G => K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)
      K ⟨le_rfl, hK⟩
  refine ⟨L, hKL, hPL.2, ?_⟩
  intro M hLM hM
  exact hmax M hLM ⟨le_trans hKL hLM, hM⟩