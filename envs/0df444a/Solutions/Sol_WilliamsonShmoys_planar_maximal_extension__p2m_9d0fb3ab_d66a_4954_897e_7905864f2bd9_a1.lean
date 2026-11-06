-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension__p2m_9d0fb3ab_d66a_4954_897e_7905864f2bd9_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:32:22.273014+00:00
-- url     : https://prove2.me/submissions/0b05a47f-a94c-497a-a594-772492dd7afb

-- ID: 98819be2-b7a0-4e40-9594-ea97bee4d16d | NAME: WilliamsonShmoys.planar_maximal_extension__p2m_9d0fb3ab_d66a_4954_897e_7905864f2bd9_a1 | 未本地编译验证
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hPlanar : HasPlanarDrawingOn J) : ∃ H : SimpleGraph V, HasPlanarDrawingOn H ∧ J.edgeSet.ncard ≤ H.edgeSet.ncard ∧ ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by
  classical
  let p : SimpleGraph V → Prop := fun H => J ≤ H ∧ HasPlanarDrawingOn H
  have hpJ : p J := ⟨le_rfl, hPlanar⟩
  obtain ⟨H, _, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := J) hpJ)
  rcases hmax with ⟨hpH, hmax'⟩
  have hsub : J.edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_subset_edgeSet.mpr hpH.1
  have hfin : H.edgeSet.Finite := Set.toFinite _
  refine ⟨H, hpH.2, Set.ncard_le_ncard hsub hfin, ?_⟩
  intro K hHK hK
  have hKH : K ≤ H := hmax' ⟨hpH.1.trans hHK, hK⟩ hHK
  exact le_antisymm hKH hHK
