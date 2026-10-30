-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_5e849ad0_992f_4795_a8f1_d28ee483fe3d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:07:30.073358+00:00
-- url     : https://prove2.me/submissions/ce0cdb86-6059-45f0-b2fd-67c85d413151

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  classical
  let S : Set (SimpleGraph V) :=
    {L | K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L}
  have hSfin : S.Finite := Set.toFinite S
  have hSnon : S.Nonempty := ⟨K, le_rfl, hDraw⟩
  obtain ⟨L, hL, hmax⟩ := hSfin.exists_maximal hSnon
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hLM hM
  have hMmem : M ∈ S := ⟨hL.1.trans hLM, hM⟩
  have hML : M ≤ L := hmax hMmem hLM
  exact le_antisymm hML hLM