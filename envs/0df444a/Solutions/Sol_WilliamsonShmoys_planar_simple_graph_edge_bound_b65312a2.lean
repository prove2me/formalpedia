-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound_b65312a2
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:17:13.655231+00:00
-- url     : https://prove2.me/submissions/4b192ab0-b8c9-41c1-82e7-f8a6db5f0196

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (M : SimpleGraph V)
        (hV : 3 ≤ Fintype.card V)
        (hMdraw : HasPlanarDrawingOn M),
        3 * Fintype.card V ≤ M.edgeSet.ncard + 6) := by
  intro hTarget
  let M : SimpleGraph (Fin 3) := ⊥
  have hV : 3 ≤ Fintype.card (Fin 3) := by simp
  have hMdraw : HasPlanarDrawingOn M := by
    let p : Fin 3 → ℝ × ℝ := fun v => ((v.val : ℝ), 0)
    let arc : Fin 3 → Fin 3 → ℝ → ℝ × ℝ := fun _ _ _ => (0, 0)
    refine ⟨p, arc, ?_, ?_, ?_⟩
    · intro x y hxy
      apply Fin.ext
      have hv : (x.val : ℝ) = (y.val : ℝ) := congrArg Prod.fst hxy
      exact_mod_cast hv
    · simp [M]
    · simp [M]
  have h := hTarget M hV hMdraw
  have hcard : M.edgeSet.ncard = 0 := by simp [M]
  rw [hcard] at h
  norm_num at h