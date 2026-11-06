-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_max_card__p2m_e1d0a0ee_343a_44fb_acd2_3b165723c48a_a3
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:00:24.643475+00:00
-- url     : https://prove2.me/submissions/3879b641-d5a1-4ebd-b2c8-5823f56ba7e9

-- ID: 57d36944-770c-4d46-99be-52926779c9ff | NAME: WilliamsonShmoys.planar_supergraph_max_card__p2m_e1d0a0ee_343a_44fb_acd2_3b165723c48a_a3 | 未本地编译验证
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) : ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → ¬ L ≤ K → Nat.card {p : V × V // K.Adj p.1 p.2} < Nat.card {p : V × V // L.Adj p.1 p.2} := by
  classical
  let p : SimpleGraph V → Prop := fun G => J ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hpJ : p J := ⟨le_rfl, hJ⟩
  obtain ⟨K, _hJK, hmax⟩ := Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := J) hpJ
  rcases hmax with ⟨hpK, hmax'⟩
  refine ⟨K, hpK.1, hpK.2, ?_⟩
  intro L hKL hL hnLK
  exfalso
  apply hnLK
  exact hmax' ⟨hpK.1.trans hKL, hL⟩ hKL
