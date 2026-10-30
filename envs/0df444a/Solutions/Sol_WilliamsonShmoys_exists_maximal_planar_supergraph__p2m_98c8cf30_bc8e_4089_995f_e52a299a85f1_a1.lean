-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_98c8cf30_bc8e_4089_995f_e52a299a85f1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:33:54.534786+00:00
-- url     : https://prove2.me/submissions/97f01807-6be0-442b-9941-5c6881e356e8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V, G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → M = N := by
  classical
  let P : SimpleGraph V → Prop := fun M => G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M
  have hfinite : {M : SimpleGraph V | P M}.Finite := Set.toFinite _
  have hnonempty : {M : SimpleGraph V | P M}.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨M, hmax⟩ := hfinite.exists_maximal hnonempty
  refine ⟨M, hmax.1.1, hmax.1.2, ?_⟩
  intro N hMN hN
  have hNmem : P N := ⟨hmax.1.1.trans hMN, hN⟩
  exact le_antisymm hMN (hmax.2 hNmem hMN)