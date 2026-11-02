-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_edge_bound_ge_three__p2m_93958b12_2978_49ef_a2e2_395a87349bb0_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:17:54.516174+00:00
-- url     : https://prove2.me/submissions/f946eb53-00f2-4971-88e4-03eff93f17fc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V), HasPlanarDrawingOn N →
    3 ≤ Fintype.card V →
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     3 * Fintype.card V ≤ N.edgeFinset.card + 6)) := by
  intro h
  let N : SimpleGraph (Fin 3) := ⊥
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  let p : Fin 3 → ℝ × ℝ := fun v => ((v.val : ℝ), 0)
  have hp : Function.Injective p := by
    intro a b hab
    apply Fin.ext
    have hreal : (a.val : ℝ) = (b.val : ℝ) := congrArg Prod.fst hab
    exact_mod_cast hreal
  have hdraw : HasPlanarDrawingOn N := by
    refine ⟨p, (fun _ _ _ => (0, 0)), hp, ?_, ?_⟩
    · intro u v huv hadj
      simp [N] at hadj
    · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
      simp [N] at hadj₁
  have hbound := h (N := N) hdraw (by norm_num)
  norm_num [N, SimpleGraph.edgeFinset] at hbound