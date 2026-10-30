-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_extend_from_curve__p2m_30cabda6_8091_40b2_a533_c24aec10a077_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:32:07.328052+00:00
-- url     : https://prove2.me/submissions/af291104-db25-4d86-beba-2e2e6e6d377e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_extend_from_clean_arc__p2m_468912c8_f62d_4992_8d85_065aef654ab4_a1__p2m_468912c8_f62d_4992_8d85_065aef654ab4_a2
import Theorems.Thm_WilliamsonShmoys_sup_inserted_nonedge_has_more_edges__p2m_468912c8_f62d_4992_8d85_065aef654ab4_a1__p2m_468912c8_f62d_4992_8d85_065aef654ab4_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdge : ∀ a b, a < b → G.Adj a b →
      ContinuousOn (arc a b) (Set.Icc 0 1) ∧
      Set.InjOn (arc a b) (Set.Icc 0 1) ∧
      arc a b 0 = p a ∧ arc a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w)
    (hCross : ∀ a b x y, a < b → x < y → G.Adj a b → G.Adj x y →
      (a, b) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc a b t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) (huv : u < v) (hnot : ¬ G.Adj u v)
    (γ : ℝ → ℝ × ℝ) (hγ_cont : ContinuousOn γ (Set.Icc 0 1))
    (hγ_inj : Set.InjOn γ (Set.Icc 0 1))
    (hγ_start : γ 0 = p u) (hγ_end : γ 1 = p v)
    (hγ_vertices : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w)
    (hγ_edges : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y →
      ∀ s ∈ Set.Icc 0 1, γ t ≠ arc x y s) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      G.edgeSet.ncard < K.edgeSet.ncard := by
  let K : SimpleGraph V := G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}
  refine ⟨K, ?_, ?_, ?_⟩
  · exact le_sup_left
  · exact WilliamsonShmoys.planarDrawingOn_extend_from_clean_arc__p2m_468912c8_f62d_4992_8d85_065aef654ab4_a1__p2m_468912c8_f62d_4992_8d85_065aef654ab4_a2
      G p arc hp hEdge hCross u v huv hnot γ hγ_cont hγ_inj hγ_start hγ_end
      hγ_vertices hγ_edges
  · exact WilliamsonShmoys.sup_inserted_nonedge_has_more_edges__p2m_468912c8_f62d_4992_8d85_065aef654ab4_a1__p2m_468912c8_f62d_4992_8d85_065aef654ab4_a2
      G u v huv hnot
