-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:27:31.434812+00:00
-- url     : https://prove2.me/submissions/927a88fd-b5a8-48de-9d1e-7584016cb126

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_graph_has_strict_planar_extension_of_three_vertices__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a2
import Theorems.Thm_WilliamsonShmoys_has_planar_drawingOn_single_edge_extension__p2m_e1c10048_df1f_49a0_8080_5a203a611921_a4

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V) (hsep : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V, G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  classical
  by_cases hV : 3 ≤ Fintype.card V
  · have hdis : ¬ G.Connected := fun h => hsep (h.preconnected u v)
    exact WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_extension_of_three_vertices__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a2
      G hG hV hdis
  · have huv : u ≠ v := by
      rintro rfl; exact hsep (SimpleGraph.Reachable.refl u)
    have hnadj : ¬ G.Adj u v := fun h => hsep h.reachable
    -- every vertex is `u` or `v`
    have hall : ∀ w : V, w = u ∨ w = v := by
      intro w
      by_contra hw
      push_neg at hw
      apply hV
      have : ({u, v, w} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hw.2)]
        simp [huv, Ne.symm hw.1]
      calc 3 = ({u, v, w} : Finset V).card := this.symm
        _ ≤ Fintype.card V := Finset.card_le_univ _
    set a := min u v with ha
    set b := max u v with hb
    have hab : a < b := by
      rcases lt_or_gt_of_ne huv with h | h
      · simp [ha, hb, min_eq_left h.le, max_eq_right h.le, h]
      · simp [ha, hb, min_eq_right h.le, max_eq_left h.le, h]
    have hall' : ∀ w : V, w = a ∨ w = b := by
      intro w
      rcases hall w with h | h <;>
      rcases lt_or_gt_of_ne huv with h' | h'
      · left; simp [ha, h, min_eq_left h'.le]
      · right; simp [hb, h, max_eq_left h'.le]
      · right; simp [hb, h, max_eq_right h'.le]
      · left; simp [ha, h, min_eq_right h'.le]
    have hane : a ≠ b := ne_of_lt hab
    let p : V → ℝ × ℝ := fun w => if w = a then (0, 0) else (1, 0)
    have hp : Function.Injective p := by
      intro x y hxy
      rcases hall' x with rfl | rfl <;> rcases hall' y with rfl | rfl
      · rfl
      · simp [p, Ne.symm hane] at hxy
      · simp [p, Ne.symm hane] at hxy
      · rfl
    let c : ℝ → ℝ × ℝ := fun t => (t, 0)
    have hTop : WilliamsonShmoys.HasPlanarDrawingOn (⊤ : SimpleGraph V) := by
      refine WilliamsonShmoys.has_planar_drawingOn_single_edge_extension__p2m_e1c10048_df1f_49a0_8080_5a203a611921_a4
        (⊥ : SimpleGraph V) ⊤ p (fun _ _ _ => (0, 0)) hp
        (by intro x y _ h; exact absurd h (by simp))
        (by intro _ _ _ _ _ _ h; simp at h)
        a b c hab ?_ ?_ ?_ ?_ ?_
        (by intro x y _ h; exact absurd h (by simp)) ?_
      · exact (continuous_id.prodMk continuous_const).continuousOn
      · intro x _ y _ h
        simpa [c] using congrArg Prod.fst h
      · simp [c, p]
      · simp [c, p, Ne.symm hane]
      · intro t ht w hw
        rcases hall' w with rfl | rfl
        · simp [c, p] at hw; linarith [ht.1, hw]
        · simp [c, p, Ne.symm hane] at hw; linarith [ht.2, hw]
      · intro x y hxy
        simp only [SimpleGraph.top_adj, SimpleGraph.bot_adj, false_or]
        constructor
        · intro _
          rcases hall' x with rfl | rfl <;> rcases hall' y with rfl | rfl
          · exact absurd hxy (lt_irrefl _)
          · exact ⟨rfl, rfl⟩
          · exact absurd (hxy.trans hab) (lt_irrefl _)
          · exact absurd hxy (lt_irrefl _)
        · rintro ⟨rfl, rfl⟩; exact hane
    refine ⟨⊤, lt_of_le_of_ne le_top ?_, hTop⟩
    intro h
    apply hnadj
    rw [h]
    exact huv
