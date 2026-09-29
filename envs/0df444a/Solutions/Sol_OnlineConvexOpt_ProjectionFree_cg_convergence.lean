-- Prove2me | solution 1 for OnlineConvexOpt.ProjectionFree.cg_convergence
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:19:08.782989+00:00
-- url     : https://prove2.me/submissions/d4399a03-c45c-4a96-b882-c04e74cda9d2

import Mathlib
import Definitions.Def_OnlineConvexOpt_ProjectionFree_ConditionalGradient
import Definitions.Def_OnlineConvexOpt_ProjectionFree_SmoothOn

namespace OnlineConvexOpt.ProjectionFree

/-- The counterexample run on `K = [0,1] ⊆ ℝ`: start at `x 1 = 1`, then jump to `0`. -/
noncomputable def aux_cgc_x : ℕ → ℝ := fun t => if t = 1 then 1 else 0

lemma aux_cgc_run :
    IsConditionalGradientRun (Set.Icc (0 : ℝ) 1) (fun _ => (3 : ℝ))
      (fun t : ℕ => min 1 (2 / (t : ℝ))) aux_cgc_x (fun _ => (0 : ℝ)) := by
  refine ⟨by simp [aux_cgc_x], ?_⟩
  intro t ht
  refine ⟨⟨by simp, ?_⟩, ?_⟩
  · intro y hy
    simp only [Real.inner_apply]
    nlinarith [hy.1]
  · rcases Nat.lt_or_ge t 2 with h | h
    · have : t = 1 := by omega
      subst this
      norm_num [aux_cgc_x]
    · have h1 : t ≠ 1 := by omega
      have h2 : t + 1 ≠ 1 := by omega
      have h3 : t ≠ 0 := by omega
      simp [aux_cgc_x, h1, h3]

end OnlineConvexOpt.ProjectionFree

open OnlineConvexOpt.ProjectionFree

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (f : E → ℝ) (g : E → E) (β : ℝ) (hβpos : 0 < β) (hsmooth : SmoothOn K f g β)
    (hfconv : ConvexOn ℝ K f)
    (xstar : E) (hxstar : xstar ∈ K) (hxstar_min : ∀ x ∈ K, f xstar ≤ f x)
    (η : ℕ → ℝ) (hη : ∀ t : ℕ, 1 ≤ t → η t = min 1 (2 / (t : ℝ)))
    (x v : ℕ → E) (hrun : IsConditionalGradientRun K g η x v)
    (t : ℕ) (ht : 1 ≤ t),
    f (x t) - f xstar ≤ 2 * β * D ^ 2 / t) := by
  intro H
  have hsm : SmoothOn (Set.Icc (0 : ℝ) 1) (fun y => 3 * y) (fun _ => (3 : ℝ)) 1 := by
    intro a _ b _
    simp only [Real.inner_apply]
    nlinarith [sq_nonneg (b - a)]
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun y => 3 * y) :=
    (LinearMap.lsmul ℝ ℝ 3).convexOn (convex_Icc 0 1)
  have hD : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, dist a b ≤ 1 := by
    intro a ha b hb
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have := H (E := ℝ) (Set.Icc 0 1) (convex_Icc 0 1) ⟨0, by simp⟩ 1 one_pos hD
    (fun y => 3 * y) (fun _ => 3) 1 one_pos hsm hconv 0 (by simp)
    (by intro y hy; linarith [hy.1])
    (fun t : ℕ => min 1 (2 / (t : ℝ))) (fun _ _ => rfl) aux_cgc_x (fun _ => 0) aux_cgc_run
    1 le_rfl
  norm_num [aux_cgc_x] at this
