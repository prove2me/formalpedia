-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_dd6ad35b_d06d_4359_826f_34a5efd43246_a1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:43:11.3552+00:00
-- url     : https://prove2.me/submissions/6053b29d-bc3f-4576-8981-c6d865e84298

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V), 3 * Fintype.card V ≤ H.edgeSet.ncard + 6) := by
  intro claimed
  -- V = Fin 3, H = ⊥ drawn with vertex i at (i, 0): the bound would read 9 ≤ 0 + 6.
  have hdraw : HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 3)) := by
    refine ⟨fun i => (((i : ℕ) : ℝ), (0 : ℝ)), fun _ _ _ => 0, ?_, ?_, ?_⟩
    · intro a b h
      simp only [Prod.mk.injEq, and_true] at h
      exact Fin.ext (by exact_mod_cast h)
    · intro u v _ h
      simp at h
    · intro u v x y _ _ h
      simp at h
  have h := claimed (⊥ : SimpleGraph (Fin 3)) hdraw (by simp)
  simp [SimpleGraph.edgeSet_bot] at h

#print axioms solution
