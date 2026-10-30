-- Prove2me | solution 2 for WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_extension__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-29T19:37:50.524406+00:00
-- url     : https://prove2.me/submissions/e476122d-aedb-4d7e-8ab0-6cc06c0bf0ff

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (G : SimpleGraph V)
        (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
        (hdis : ¬ G.Connected),
        ∃ H : SimpleGraph V, G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H) := by
  intro hall
  let G : SimpleGraph (Fin 0) := ⊥
  have hG : WilliamsonShmoys.HasPlanarDrawingOn G := by
    let p : Fin 0 → ℝ × ℝ := fun v => Fin.elim0 v
    let arc : Fin 0 → Fin 0 → ℝ → ℝ × ℝ := fun u => Fin.elim0 u
    refine ⟨p, arc, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro u v
      exact Fin.elim0 u
    · intro u v huv hadj
      exact Fin.elim0 u
    · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
      exact Fin.elim0 u
  have hdis : ¬ G.Connected := by
    intro hc
    rcases hc.nonempty with ⟨v⟩
    exact Fin.elim0 v
  obtain ⟨H, hlt, _⟩ := hall (V := Fin 0) G hG hdis
  have hHG : H = G := by
    ext u v
    exact Fin.elim0 u
  subst H
  exact (lt_irrefl G) hlt