-- Prove2me | solution 1 for UCConvexHull.OneUC.oneSum_convex_closed
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T00:57:21.002482+00:00
-- url     : https://prove2.me/submissions/2724aa91-df2c-4f9a-8ee7-7cbd762464ae

import Mathlib
import Definitions.Def_UCConvexHull_OneUC_HullTools

open UCConvexHull.OneUC in
theorem solution {n₁ n₂ : ℕ} (S₁ : Set ((Fin n₁ → ℝ) × ℝ))
    (S₂ : Set ((Fin n₂ → ℝ) × ℝ)) :
    (Convex ℝ S₁ → Convex ℝ S₂ → Convex ℝ (oneSum S₁ S₂)) ∧
      (IsClosed S₁ → IsClosed S₂ → IsClosed (oneSum S₁ S₂)) := by
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · intro x hx y hy a b ha hb hab
    refine ⟨?_, ?_⟩
    · have := h1 hx.1 hy.1 ha hb hab
      convert this using 1; ext <;> simp
    · have := h2 hx.2 hy.2 ha hb hab
      convert this using 1; ext <;> simp
  · have e : oneSum S₁ S₂ =
        (fun q : (Fin n₁ → ℝ) × (Fin n₂ → ℝ) × ℝ => (q.1, q.2.2)) ⁻¹' S₁ ∩
        (fun q : (Fin n₁ → ℝ) × (Fin n₂ → ℝ) × ℝ => (q.2.1, q.2.2)) ⁻¹' S₂ := rfl
    rw [e]
    exact (h1.preimage (by fun_prop)).inter (h2.preimage (by fun_prop))
