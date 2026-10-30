-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_disconnected_path__p2m_635a1d24_9162_4bc8_8f51_e7db8e0ee893_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:01:20.792003+00:00
-- url     : https://prove2.me/submissions/d061653b-3b31-4029-a135-a1f9076fc07f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_disconnected_path_augmentation__p2m_100679c8_dd25_4620_924f_9d4949429e29_a3__p2m_100679c8_dd25_4620_924f_9d4949429e29_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 <= Fintype.card V) (G : SimpleGraph V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdge : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hCross : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hG_not_connected : ¬ G.Connected) :
    ∃ u v, u < v ∧ ¬ G.Reachable u v ∧ ∃ γ : ℝ → ℝ × ℝ,
      ContinuousOn γ (Set.Icc 0 1) ∧ γ 0 = p u ∧ γ 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y →
        ∀ s ∈ Set.Icc 0 1, γ t ≠ arc x y s) := by
  obtain ⟨H, q, u, v, hSub, huv, hUnreach, hHuv, hNotGuv, hDraw, hAgree⟩ :=
    WilliamsonShmoys.planarDrawingOn_disconnected_path_augmentation__p2m_100679c8_dd25_4620_924f_9d4949429e29_a3__p2m_100679c8_dd25_4620_924f_9d4949429e29_a4
      hV G p arc hp hEdge hCross hG_not_connected
  have hQ := hDraw u v huv hHuv
  refine ⟨u, v, huv, hUnreach, q u v, hQ.1, hQ.2.2.1, hQ.2.2.2.1,
    hQ.2.2.2.2.1, ?_⟩
  intro t ht x y hxy hGxy s hs heq
  have hHxy : H.Adj x y := hSub hGxy
  have heqQ : q u v t = q x y s := by
    calc
      q u v t = arc x y s := heq
      _ = q x y s := (hAgree x y hxy hGxy s hs).symm
  have hpairs : (u, v) ≠ (x, y) := by
    intro he
    have hux : u = x := congrArg Prod.fst he
    have hvy : v = y := congrArg Prod.snd he
    subst x
    subst y
    exact hNotGuv hGxy
  have hc := hQ.2.2.2.2.2 x y hxy hHxy hpairs t
    (Set.Ioo_subset_Icc_self ht) s hs heqQ
  rcases hc.1 with hzero | hone
  · exact (ne_of_gt ht.1) hzero
  · exact (ne_of_lt ht.2) hone
