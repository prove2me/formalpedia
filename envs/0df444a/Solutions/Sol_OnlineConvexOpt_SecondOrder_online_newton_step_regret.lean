-- Prove2me | solution 1 for OnlineConvexOpt.SecondOrder.online_newton_step_regret
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:49:43.026494+00:00
-- url     : https://prove2.me/submissions/5236d9cc-9572-42e6-9efb-c7f32ba90ce6

import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave
import Definitions.Def_OnlineConvexOpt_SecondOrder_OnlineNewtonStep
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open OnlineConvexOpt.SecondOrder OnlineConvexOpt.FirstOrder


namespace OnlineConvexOpt.SecondOrder

theorem onsg_grad_const {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (c : ℝ) (p : E) : HasGradientAt (fun _ : E => c) (0:E) p := by
  have h := hasFDerivAt_const (𝕜 := ℝ) c p
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa using h

theorem onsg_grad_unique {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (c : ℝ) (p v : E) (h : HasGradientAt (fun _ : E => c) v p) : v = (0:E) := by
  have h1 := h.hasFDerivAt.unique (hasFDerivAt_const c p)
  have : (InnerProductSpace.toDual ℝ E) v = (InnerProductSpace.toDual ℝ E) 0 := by
    rw [map_zero]; exact h1
  exact (InnerProductSpace.toDual ℝ E).injective this

theorem onsg_regret {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (c : ℝ) (hc : 0 ≤ c) (x : ℕ → E) (T : ℕ) (y0 : E) (hy0 : y0 ∉ K) :
    (T : ℝ) * c ≤ RegretT K (fun _ _ => c) x T := by
  unfold RegretT
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hbdd : BddBelow (Set.range fun y : E => ⨅ (_ : y ∈ K), (T:ℝ) * c) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    dsimp only
    by_cases hy : y ∈ K
    · rw [ciInf_pos hy]; positivity
    · rw [ciInf_neg hy]; simp
  have hle : (⨅ y ∈ K, (T:ℝ) * c) ≤ 0 := by
    refine (ciInf_le hbdd y0).trans ?_
    rw [ciInf_neg hy0]; simp
  linarith

theorem onsg_counter : ¬ (∀ (n : ℕ) (hn : 2 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (α D G : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (hD : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ D)
    (hG : ∀ t, ∀ p ∈ K, ∀ v, HasGradientAt (f t) v p → ‖v‖ ≤ G)
    (hα : 0 < α) (hGpos : 0 < G) (hDpos : 0 < D)
    (γ ε : ℝ) (hγ : γ = (1 / 2) * min (1 / (G * D)) α) (hε : ε = 1 / (γ ^ 2 * D ^ 2))
    (x g : ℕ → EuclideanSpace ℝ (Fin n))
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hONS : IsOnlineNewtonStep K γ ε f x g A)
    (T : ℕ) (hT : 4 ≤ T),
    RegretT K f x T ≤ 2 * (1 / α + G * D) * n * Real.log T) := by
  intro H
  set γ : ℝ := (1 / 2) * min (1 / (1 * 1)) 1
  set ε : ℝ := 1 / (γ ^ 2 * 1 ^ 2)
  let K : Set (EuclideanSpace ℝ (Fin 2)) := {0}
  have hONS : IsOnlineNewtonStep K γ ε (fun _ _ => (100:ℝ)) (fun _ => 0) (fun _ => 0)
      (fun _ => ε • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) := by
    refine ⟨rfl, rfl, fun t => onsg_grad_const _ _, fun t => ?_, fun t => ⟨rfl, ?_⟩⟩
    · ext; simp
    · intro z hz; rw [Set.mem_singleton_iff.mp hz]
  have hf : ∀ t : ℕ, IsExpConcaveOn 1 K ((fun _ _ => (100:ℝ)) t) :=
    fun t => ⟨convexOn_const _ (convex_singleton 0), concaveOn_const _ (convex_singleton 0)⟩
  have h := H 2 le_rfl K 1 1 1 (fun _ _ => (100:ℝ)) hf
    (fun p hp q hq => by rw [Set.mem_singleton_iff.mp hp, Set.mem_singleton_iff.mp hq]; simp)
    (fun t p _ v hv => by rw [onsg_grad_unique _ _ _ hv]; simp)
    one_pos one_pos one_pos γ ε rfl rfl _ _ _ hONS 4 le_rfl
  have hne : EuclideanSpace.single (0 : Fin 2) (1:ℝ) ∉ K := by
    intro hm
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) (Set.mem_singleton_iff.mp hm)
    simp at this
  have h2 := onsg_regret K 100 (by norm_num) (fun _ => (0:EuclideanSpace ℝ (Fin 2))) 4 _ hne
  have hlog : Real.log (4:ℕ) ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < (4:ℕ) by norm_num)
    norm_num at this ⊢; linarith
  norm_num at h2 h hlog
  nlinarith

end OnlineConvexOpt.SecondOrder

open OnlineConvexOpt.SecondOrder


theorem solution : ¬ (∀ (n : ℕ) (hn : 2 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (α D G : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (hD : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ D)
    (hG : ∀ t, ∀ p ∈ K, ∀ v, HasGradientAt (f t) v p → ‖v‖ ≤ G)
    (hα : 0 < α) (hGpos : 0 < G) (hDpos : 0 < D)
    (γ ε : ℝ) (hγ : γ = (1 / 2) * min (1 / (G * D)) α) (hε : ε = 1 / (γ ^ 2 * D ^ 2))
    (x g : ℕ → EuclideanSpace ℝ (Fin n))
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hONS : IsOnlineNewtonStep K γ ε f x g A)
    (T : ℕ) (hT : 4 ≤ T),
    RegretT K f x T ≤ 2 * (1 / α + G * D) * n * Real.log T) := OnlineConvexOpt.SecondOrder.onsg_counter
