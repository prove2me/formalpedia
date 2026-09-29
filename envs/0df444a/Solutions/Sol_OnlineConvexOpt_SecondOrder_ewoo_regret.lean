-- Prove2me | solution 1 for OnlineConvexOpt.SecondOrder.ewoo_regret
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:51:15.101997+00:00
-- url     : https://prove2.me/submissions/15d8ab72-78f9-4362-96eb-7895fd9ddca1

import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave
import Definitions.Def_OnlineConvexOpt_SecondOrder_EWOO
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open MeasureTheory OnlineConvexOpt.SecondOrder OnlineConvexOpt.FirstOrder


namespace OnlineConvexOpt.SecondOrder

theorem ewoo_regret_lb {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

theorem ewoo_counter : ¬ (∀ (n : ℕ) (hn : 0 < n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKconv : Convex ℝ K) (hKne : K.Nonempty) (hKbdd : Bornology.IsBounded K)
    (hKmeas : MeasurableSet K) (hKvol : 0 < volume K)
    (α : ℝ) (hα : 0 < α) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hEWOO : IsEWOO K α f x)
    (T : ℕ) (hT : 1 ≤ T),
    RegretT K f x T ≤ (n / α) * Real.log T + 2 / α) := by
  intro H
  let K : Set (EuclideanSpace ℝ (Fin 1)) := Metric.ball 0 1
  let f : ℕ → EuclideanSpace ℝ (Fin 1) → ℝ := fun _ _ => 100
  have hf : ∀ t : ℕ, IsExpConcaveOn 1 K (f t) :=
    fun t => ⟨convexOn_const _ (convex_ball (0 : EuclideanSpace ℝ (Fin 1)) 1), concaveOn_const (Real.exp (-1 * 100)) (convex_ball (0 : EuclideanSpace ℝ (Fin 1)) 1)⟩
  have h := H 1 one_pos K (convex_ball (0 : EuclideanSpace ℝ (Fin 1)) 1) ⟨0, Metric.mem_ball_self one_pos⟩
    Metric.isBounded_ball measurableSet_ball (Metric.measure_ball_pos volume 0 one_pos)
    1 one_pos f hf _ (fun t => rfl) 1 le_rfl
  have hne : EuclideanSpace.single (0 : Fin 1) (1:ℝ) ∉ K := by
    intro hm
    simp [K] at hm
  have h2 := ewoo_regret_lb K 100 (by norm_num) (fun t => (∫ y in K, ewooWeight 1 f t y ∂volume)⁻¹ •
    ∫ y in K, ewooWeight 1 f t y • y ∂volume) 1 _ hne
  norm_num at h2 h
  linarith

end OnlineConvexOpt.SecondOrder

open OnlineConvexOpt.SecondOrder


theorem solution : ¬ (∀ (n : ℕ) (hn : 0 < n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKconv : Convex ℝ K) (hKne : K.Nonempty) (hKbdd : Bornology.IsBounded K)
    (hKmeas : MeasurableSet K) (hKvol : 0 < volume K)
    (α : ℝ) (hα : 0 < α) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hEWOO : IsEWOO K α f x)
    (T : ℕ) (hT : 1 ≤ T),
    RegretT K f x T ≤ (n / α) * Real.log T + 2 / α) := OnlineConvexOpt.SecondOrder.ewoo_counter
