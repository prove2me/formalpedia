-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_drawable_supergraph__p2m_09b502cd_aaf2_445b_949d_80cdcc13c52d_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:00:56.999878+00:00
-- url     : https://prove2.me/submissions/0de62404-df21-45a7-ac7f-c82e41a9c12f

-- ID: 27628b41-9b86-421c-a9af-b79318367974 | NAME: WilliamsonShmoys.planar_maximal_drawable_supergraph__p2m_09b502cd_aaf2_445b_949d_80cdcc13c52d_a1 | 未本地编译验证
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) : Exists fun M : SimpleGraph V => Set.Subset H.edgeSet M.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ ∀ N : SimpleGraph V, Set.Subset M.edgeSet N.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by
  classical
  let p : SimpleGraph V → Prop := fun M => Set.Subset H.edgeSet M.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn M
  have hpH : p H := ⟨fun e he => he, hDraw⟩
  obtain ⟨M, _hHM, hmax⟩ := Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := H) hpH
  rcases hmax with ⟨hpM, hmax'⟩
  refine ⟨M, hpM.1, hpM.2, ?_⟩
  intro N hMN hN
  have hMN' : M ≤ N := SimpleGraph.edgeSet_subset_edgeSet.mp hMN
  have hpN : p N := ⟨fun e he => hMN (hpM.1 he), hN⟩
  have hNM : N ≤ M := hmax' hpN hMN'
  exact le_antisymm hNM hMN'
