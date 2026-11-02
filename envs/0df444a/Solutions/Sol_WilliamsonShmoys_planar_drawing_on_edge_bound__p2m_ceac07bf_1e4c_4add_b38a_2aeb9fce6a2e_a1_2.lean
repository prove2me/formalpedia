-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_on_edge_bound__p2m_ceac07bf_1e4c_4add_b38a_2aeb9fce6a2e_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:22:24.150052+00:00
-- url     : https://prove2.me/submissions/fb84767e-4448-4d1a-aa7f-a814a6159468

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V), HasPlanarDrawingOn N →
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
  have hbound := h (N := N) hdraw
  norm_num [N, SimpleGraph.edgeFinset] at hbound