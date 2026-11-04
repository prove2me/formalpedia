-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_a6656023_52ae_443d_ab7b_e0c464fa9c80_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:36:30.813434+00:00
-- url     : https://prove2.me/submissions/b7aa7b70-335d-46d4-bd8d-b50202db8a5d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (M : SimpleGraph V),
        3 ≤ Fintype.card V → HasPlanarDrawingOn M →
        3 * Fintype.card V - 6 ≤
          (letI : DecidableRel M.Adj := Classical.decRel M.Adj
           M.edgeFinset.card)) := by
  classical
  intro h
  let M : SimpleGraph (Fin 3) := ⊥
  have hdraw : HasPlanarDrawingOn M := by
    unfold HasPlanarDrawingOn
    let p : Fin 3 → ℝ × ℝ := fun v => (v.val, 0)
    let arc : Fin 3 → Fin 3 → ℝ → ℝ × ℝ := fun _ _ _ => (0, 0)
    refine ⟨p, ?_⟩
    refine ⟨arc, ?_⟩
    constructor
    · intro a b hab
      have hfst : (a.val : ℝ) = (b.val : ℝ) := by
        simpa [p] using congrArg Prod.fst hab
      exact Fin.ext (by exact_mod_cast hfst)
    constructor
    · intro u v huv hadj
      simp [M] at hadj
    · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
      simp [M] at hadj
  have hbad := h M (by norm_num : 3 ≤ Fintype.card (Fin 3)) hdraw
  have hempty (i : Fintype M.edgeSet) :
      @SimpleGraph.edgeFinset (Fin 3) M i = ∅ := by
    ext e
    simp [M]
  rw [hempty _] at hbad
  norm_num at hbad