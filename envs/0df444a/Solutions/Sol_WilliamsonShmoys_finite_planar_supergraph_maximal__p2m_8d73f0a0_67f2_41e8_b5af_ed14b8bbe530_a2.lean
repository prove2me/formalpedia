-- Prove2me | solution 1 for WilliamsonShmoys.finite_planar_supergraph_maximal__p2m_8d73f0a0_67f2_41e8_b5af_ed14b8bbe530_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:38:55.389412+00:00
-- url     : https://prove2.me/submissions/cc4a2b81-9047-4034-80ad-c7f9db067590

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by
  classical
  let P : SimpleGraph V → Prop := fun M => K ≤ M ∧ HasPlanarDrawingOn M
  have hKmem : K ∈ {M : SimpleGraph V | P M} := ⟨le_rfl, hK⟩
  have hfinite : ({M : SimpleGraph V | P M} : Set (SimpleGraph V)).Finite := Set.toFinite _
  obtain ⟨L, hKL, hmax⟩ := hfinite.exists_le_maximal hKmem
  rcases (maximal_mem_iff).1 hmax with ⟨hLmem, hmax⟩
  refine ⟨L, hLmem.1, hLmem.2, ?_⟩
  intro M hLM hM
  have hMmem : M ∈ {M : SimpleGraph V | P M} := ⟨le_trans hLmem.1 hLM, hM⟩
  exact (hmax hMmem hLM).symm