-- Prove2me | solution 2 for WilliamsonShmoys.planar_graph_connected_completion_from_bridge_property__p2m_e87f3d6d_f5ac_4caa_95af_19e806d71ee4_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:31:21.077192+00:00
-- url     : https://prove2.me/submissions/5198944f-3e4d-4b2a-8f5e-d14eeb0d1511

-- ID: 39b2e6d4-604e-4f41-9365-8bd67e4be3f2 | NAME: WilliamsonShmoys.planar_graph_connected_completion_from_bridge_property__p2m_e87f3d6d_f5ac_4caa_95af_19e806d71ee4_a2 | 未本地编译验证
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P M)
    (hne : Nonempty V)
    (hbridge : ∀ (G : SimpleGraph V), P G →
      ∀ x y : V, ¬ G.Reachable x y →
        ∃ N : SimpleGraph V,
          G ≤ N ∧
          (∀ u v, N.Adj u v ↔
            G.Adj u v ∨ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) ∧
          P N) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ (∀ x y, N.Reachable x y) ∧ P N := by
  classical
  let p : SimpleGraph V → Prop := fun G => M ≤ G ∧ P G
  have hpM : p M := ⟨le_rfl, hP⟩
  obtain ⟨H, _hMH, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := M) hpM)
  rcases hmax with ⟨hpH, hmax'⟩
  by_cases hpre : ∀ x y : V, H.Reachable x y
  · exact ⟨H, hpH.1, hpre, hpH.2⟩
  · exfalso
    simp only [not_forall] at hpre
    obtain ⟨x, y, hxy⟩ := hpre
    obtain ⟨N, hHN, hadj, hPN⟩ := hbridge H hpH.2 x y hxy
    have hNxy : N.Adj x y := by
      rw [hadj x y]
      simp
    have hHnxy : ¬ H.Adj x y := fun h => hxy h.reachable
    have hneHN : H ≠ N := by
      intro heq
      exact hHnxy (by simpa [heq] using hNxy)
    have hpN : p N := ⟨hpH.1.trans hHN, hPN⟩
    have hNH : N ≤ H := hmax' hpN hHN
    exact hHnxy (hNH hNxy)
