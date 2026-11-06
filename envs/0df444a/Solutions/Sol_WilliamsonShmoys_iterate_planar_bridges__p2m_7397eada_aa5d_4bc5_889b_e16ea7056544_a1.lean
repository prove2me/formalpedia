-- Prove2me | solution 1 for WilliamsonShmoys.iterate_planar_bridges__p2m_7397eada_aa5d_4bc5_889b_e16ea7056544_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:01:23.884724+00:00
-- url     : https://prove2.me/submissions/e46b0704-9977-4316-a86d-d469a5786086

-- ID: a6c61c44-359d-4d57-8094-2c2773f7c78b | NAME: WilliamsonShmoys.iterate_planar_bridges__p2m_7397eada_aa5d_4bc5_889b_e16ea7056544_a1 | 未本地编译验证
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hstep : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → ¬ K.Connected → ∃ L : SimpleGraph V, K ≤ L ∧ K.edgeSet.ncard < L.edgeSet.ncard ∧ HasPlanarDrawingOn L) : ∃ G : SimpleGraph V, H ≤ G ∧ G.Connected ∧ HasPlanarDrawingOn G := by
  classical
  let p : SimpleGraph V → Prop := fun G => H ≤ G ∧ HasPlanarDrawingOn G
  have hpH : p H := ⟨le_rfl, hH⟩
  obtain ⟨G, _hHG, hmax⟩ := Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := H) hpH
  rcases hmax with ⟨hpG, hmax'⟩
  by_cases hc : G.Connected
  · exact ⟨G, hpG.1, hc, hpG.2⟩
  · exfalso
    obtain ⟨L, hGL, hlt, hL⟩ := hstep G hpG.1 hpG.2 hc
    have hpL : p L := ⟨hpG.1.trans hGL, hL⟩
    have hLG : L ≤ G := hmax' hpL hGL
    have hEq : L = G := le_antisymm hLG hGL
    rw [hEq] at hlt
    omega
