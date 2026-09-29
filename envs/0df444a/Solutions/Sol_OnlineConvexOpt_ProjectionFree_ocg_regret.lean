-- Prove2me | solution 1 for OnlineConvexOpt.ProjectionFree.ocg_regret
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:11:40.399062+00:00
-- url     : https://prove2.me/submissions/cd19a0ec-12e1-4aea-a8fc-27917389a050

import Mathlib
import Definitions.Def_OnlineConvexOpt_ProjectionFree_AggregateFunction

open scoped InnerProductSpace
open OnlineConvexOpt.ProjectionFree

namespace OnlineConvexOpt.ProjectionFree

theorem ocg_counter : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (G : ℝ) (hGpos : 0 < G)
    (f : ℕ → E → ℝ) (hfG : ∀ t, ∀ x ∈ K, ∀ y ∈ K, |f t x - f t y| ≤ G * dist x y)
    (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (gradf : ℕ → E) (x1 : E) (hx1 : x1 ∈ K)
    (T : ℕ) (hT : 1 ≤ T)
    (η : ℝ) (hη : η = D / (2 * G * (T : ℝ) ^ (3 / 4 : ℝ)))
    (σ : ℕ → ℝ) (hσ : ∀ t : ℕ, 1 ≤ t → σ t = min 1 (2 / Real.sqrt t))
    (x v : ℕ → E) (hrun : IsOnlineConditionalGradientRun K f gradf x1 η σ x v),
    (∑ t ∈ Finset.Icc 1 T, f t (x t)) - ⨅ xstar ∈ K, ∑ t ∈ Finset.Icc 1 T, f t xstar ≤
      8 * D * G * (T : ℝ) ^ (3 / 4 : ℝ)) := by
  intro H
  have hK0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hgrad : ∀ y : ℝ, HasGradientAt (fun _ : ℝ => (100:ℝ)) 0 y := fun y =>
    (hasDerivAt_const y (100:ℝ)).hasGradientAt'
  have hrun : IsOnlineConditionalGradientRun (Set.Icc (0:ℝ) 1) (fun _ _ => (100:ℝ))
      (fun _ => (0:ℝ)) 0 (1 / (2 * 1 * ((1:ℕ):ℝ) ^ (3 / 4 : ℝ)))
      (fun t => min 1 (2 / Real.sqrt t)) (fun _ => 0) (fun _ => 0) := by
    refine ⟨rfl, hK0, fun t _ => hgrad 0, fun t _ => ⟨hK0, fun y _ => ?_⟩, fun t _ => by simp⟩
    simp [AggregateGradient]
  have h := H (Set.Icc (0:ℝ) 1) (convex_Icc 0 1) ⟨0, hK0⟩ 1 one_pos
    (fun a ha b hb => by
      rw [Real.dist_eq, abs_le]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2])
    1 one_pos (fun _ _ => (100:ℝ)) (fun t a _ b _ => by simp)
    (fun t => convexOn_const _ (convex_Icc 0 1)) (fun _ => (0:ℝ)) 0 hK0 1 le_rfl
    _ rfl (fun t => min 1 (2 / Real.sqrt t)) (fun t _ => rfl) (fun _ => 0) (fun _ => 0) hrun
  have hbdd : BddBelow (Set.range fun y : ℝ =>
      ⨅ (_ : y ∈ Set.Icc (0:ℝ) 1), ∑ t ∈ Finset.Icc 1 1, (fun (_ : ℕ) (_ : ℝ) => (100:ℝ)) t y) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    dsimp only
    by_cases hy : y ∈ Set.Icc (0:ℝ) 1
    · rw [ciInf_pos hy]; simp
    · rw [ciInf_neg hy]; simp
  have hle : (⨅ y ∈ Set.Icc (0:ℝ) 1,
      ∑ t ∈ Finset.Icc 1 1, (fun (_ : ℕ) (_ : ℝ) => (100:ℝ)) t y) ≤ 0 := by
    refine (ciInf_le hbdd 2).trans ?_
    rw [ciInf_neg (show (2:ℝ) ∉ Set.Icc (0:ℝ) 1 from fun h => by linarith [h.2])]
    simp
  simp only [Nat.cast_one, Real.one_rpow, Finset.Icc_self, Finset.sum_singleton] at h hle
  linarith

end OnlineConvexOpt.ProjectionFree

open OnlineConvexOpt.ProjectionFree

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (G : ℝ) (hGpos : 0 < G)
    (f : ℕ → E → ℝ) (hfG : ∀ t, ∀ x ∈ K, ∀ y ∈ K, |f t x - f t y| ≤ G * dist x y)
    (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (gradf : ℕ → E) (x1 : E) (hx1 : x1 ∈ K)
    (T : ℕ) (hT : 1 ≤ T)
    (η : ℝ) (hη : η = D / (2 * G * (T : ℝ) ^ (3 / 4 : ℝ)))
    (σ : ℕ → ℝ) (hσ : ∀ t : ℕ, 1 ≤ t → σ t = min 1 (2 / Real.sqrt t))
    (x v : ℕ → E) (hrun : IsOnlineConditionalGradientRun K f gradf x1 η σ x v),
    (∑ t ∈ Finset.Icc 1 T, f t (x t)) - ⨅ xstar ∈ K, ∑ t ∈ Finset.Icc 1 T, f t xstar ≤
      8 * D * G * (T : ℝ) ^ (3 / 4 : ℝ)) :=
  OnlineConvexOpt.ProjectionFree.ocg_counter
