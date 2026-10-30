-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension__p2m_316c89ef_5381_45bf_ad7e_e8d13020052b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:58:00.927538+00:00
-- url     : https://prove2.me/submissions/bef45b54-f464-4ce4-97ba-f4209f6e909c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_planar_predicate_maximal_extension__p2m_03e90475_cbaa_4d30_84cc_f87b4a621968_a1
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph__p2m_03e90475_cbaa_4d30_84cc_f87b4a621968_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (∃ (_ : DecidableRel L.Adj),
        ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.finite_planar_predicate_maximal_extension__p2m_03e90475_cbaa_4d30_84cc_f87b4a621968_a1
      (P := HasPlanarDrawingOn)
      (hdown := fun {G H} hGH hH =>
        WilliamsonShmoys.planarDrawingOn_subgraph__p2m_03e90475_cbaa_4d30_84cc_f87b4a621968_a1
          hGH hH)
      K hK
  refine ⟨L, hKL, hL, ?_⟩
  letI : DecidableRel L.Adj := Classical.decRel _
  exact ⟨inferInstance, hmax⟩