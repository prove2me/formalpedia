-- Prove2me | solution 1 for OnlineConvexOpt.SecondOrder.online_newton_step_regret_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:48:30.009273+00:00
-- url     : https://prove2.me/submissions/bf4ba749-7250-4973-8900-d456d7f0e522

import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave
import Definitions.Def_OnlineConvexOpt_SecondOrder_OnlineNewtonStep
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open OnlineConvexOpt.SecondOrder OnlineConvexOpt.FirstOrder


namespace OnlineConvexOpt.SecondOrder

theorem onsb_grad_const {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (c : ℝ) (p : E) : HasGradientAt (fun _ : E => c) (0:E) p := by
  have h := hasFDerivAt_const (𝕜 := ℝ) c p
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa using h

theorem onsb_grad_unique {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (c : ℝ) (p v : E) (h : HasGradientAt (fun _ : E => c) v p) : v = (0:E) := by
  have h1 := h.hasFDerivAt.unique (hasFDerivAt_const c p)
  have : (InnerProductSpace.toDual ℝ E) v = (InnerProductSpace.toDual ℝ E) 0 := by
    rw [map_zero]; exact h1
  exact (InnerProductSpace.toDual ℝ E).injective this

theorem onsb_regret {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

theorem onsb_counter : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (α D G γ ε : ℝ) (f : ℕ → E → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (hD : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ D)
    (hG : ∀ t, ∀ p ∈ K, ∀ v, HasGradientAt (f t) v p → ‖v‖ ≤ G)
    (hα : 0 < α) (hGpos : 0 < G) (hDpos : 0 < D)
    (hγ : γ = (1 / 2) * min (1 / (G * D)) α) (hε : ε = 1 / (γ ^ 2 * D ^ 2))
    (x g : ℕ → E) (A : ℕ → E →L[ℝ] E) (hONS : IsOnlineNewtonStep K γ ε f x g A)
    (T : ℕ),
    RegretT K f x T ≤
      (1 / α + G * D) *
        ((∑ t ∈ Finset.range T, quadForm (A (t + 1)).inverse (g t)) + 1)) := by
  intro H
  set γ : ℝ := (1 / 2) * min (1 / (1 * 1)) 1
  set ε : ℝ := 1 / (γ ^ 2 * 1 ^ 2)
  have hONS : IsOnlineNewtonStep ({0} : Set ℝ) γ ε (fun _ _ => (100:ℝ)) (fun _ => 0) (fun _ => 0)
      (fun _ => ε • ContinuousLinearMap.id ℝ ℝ) := by
    refine ⟨rfl, rfl, fun t => onsb_grad_const _ _, fun t => ?_, fun t => ⟨rfl, ?_⟩⟩
    · ext; simp
    · intro z hz; rw [Set.mem_singleton_iff.mp hz]
  have hf : ∀ t : ℕ, IsExpConcaveOn 1 ({0} : Set ℝ) ((fun _ _ => (100:ℝ)) t) :=
    fun t => ⟨convexOn_const _ (convex_singleton 0), concaveOn_const _ (convex_singleton 0)⟩
  have h := H ({0} : Set ℝ) 1 1 1 γ ε (fun _ _ => (100:ℝ)) hf
    (fun p hp q hq => by rw [Set.mem_singleton_iff.mp hp, Set.mem_singleton_iff.mp hq]; simp)
    (fun t p _ v hv => by rw [onsb_grad_unique _ _ _ hv]; simp)
    one_pos one_pos one_pos rfl rfl _ _ _ hONS 1
  have h2 := onsb_regret ({0} : Set ℝ) 100 (by norm_num) (fun _ => (0:ℝ)) 1 1 (by simp)
  simp [quadForm] at h
  norm_num at h2
  linarith

end OnlineConvexOpt.SecondOrder

open OnlineConvexOpt.SecondOrder


theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (α D G γ ε : ℝ) (f : ℕ → E → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (hD : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ D)
    (hG : ∀ t, ∀ p ∈ K, ∀ v, HasGradientAt (f t) v p → ‖v‖ ≤ G)
    (hα : 0 < α) (hGpos : 0 < G) (hDpos : 0 < D)
    (hγ : γ = (1 / 2) * min (1 / (G * D)) α) (hε : ε = 1 / (γ ^ 2 * D ^ 2))
    (x g : ℕ → E) (A : ℕ → E →L[ℝ] E) (hONS : IsOnlineNewtonStep K γ ε f x g A)
    (T : ℕ),
    RegretT K f x T ≤
      (1 / α + G * D) *
        ((∑ t ∈ Finset.range T, quadForm (A (t + 1)).inverse (g t)) + 1)) := OnlineConvexOpt.SecondOrder.onsb_counter
