-- Prove2me | solution 1 for OnlineConvexOpt.Regularization.rftl_regret_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:06:56.505962+00:00
-- url     : https://prove2.me/submissions/13ea8b17-d298-42d6-90a0-a873bd607435

import Mathlib
import Definitions.Def_OnlineConvexOpt_Regularization_Protocol
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open scoped InnerProductSpace
open OnlineConvexOpt.Regularization OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.Regularization

theorem rftl_counter : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (R : E → ℝ) (hRconv : ConvexOn ℝ K R) (gradR : E → E)
    (hgradR : ∀ x ∈ K, HasGradientAt R (gradR x) x)
    (η : ℝ) (hη : 0 < η) (f : ℕ → E → ℝ) (x grad : ℕ → E)
    (hRun : IsRFTLRun K R η f x grad)
    (nsq : ℕ → ℝ) (hnsq : ∀ t, IsLocalDualNormSq R gradR (x t) (x (t + 1)) (grad t) (nsq t))
    (T : ℕ) (u : E) (hu : u ∈ K),
    RegretT K f x T ≤
      2 * η * (∑ t ∈ Finset.range T, nsq t) + (R u - R (x 0)) / η) := by
  intro H
  have hK0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hR : ∀ y : ℝ, HasGradientAt (fun y : ℝ => y ^ 2 / 2) y y := by
    intro y
    exact (((hasDerivAt_pow 2 y).div_const 2).congr_deriv (by ring)).hasGradientAt'
  have hf : HasGradientAt (fun y : ℝ => -y ^ 2) 0 0 := by
    exact (((hasDerivAt_pow 2 (0:ℝ)).neg).congr_deriv (by ring)).hasGradientAt'
  have hconv : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun y : ℝ => y ^ 2 / 2) := by
    have := ((convexOn_pow 2).subset (fun y hy => (hy.1 : (0:ℝ) ≤ y)) (convex_Icc 0 1))
    simpa [div_eq_mul_inv, mul_comm] using this.smul (c := (1/2 : ℝ)) (by norm_num)
  have hRun : IsRFTLRun (Set.Icc (0:ℝ) 1) (fun y : ℝ => y ^ 2 / 2) 1 (fun _ y => -y ^ 2)
      (fun _ => 0) (fun _ => 0) := by
    refine ⟨⟨hK0, fun y hy => by show (0:ℝ)^2/2 ≤ y^2/2; nlinarith [sq_nonneg y]⟩, fun t => hf, fun t => ⟨hK0, fun y hy => ?_⟩⟩
    show (1:ℝ) * (∑ s ∈ Finset.range (t + 1), ⟪(0:ℝ), (0:ℝ)⟫_ℝ) + (0:ℝ)^2/2 ≤
      1 * (∑ s ∈ Finset.range (t + 1), ⟪(0:ℝ), y⟫_ℝ) + y^2/2
    simp only [inner_zero_left, Finset.sum_const_zero, mul_zero, zero_add]
    nlinarith [sq_nonneg y]
  have hnsq : ∀ t, IsLocalDualNormSq (fun y : ℝ => y ^ 2 / 2) id ((fun _ => (0:ℝ)) t)
      ((fun _ => (0:ℝ)) (t + 1)) ((fun _ => (0:ℝ)) t) 0 := by
    intro t
    refine ⟨0, ContinuousLinearMap.id ℝ ℝ, ⟨le_rfl, zero_le_one⟩, hasFDerivAt_id _, ?_, ⟨1, one_pos, fun w => ?_⟩, ?_, ?_⟩
    · exact IsSelfAdjoint.one (R := ℝ →L[ℝ] ℝ)
    · simp [quadForm, real_inner_self_eq_norm_sq]
    · simp [BregmanDivergence, quadForm]
    · simp [quadForm]
  have := H (Set.Icc (0:ℝ) 1) (convex_Icc 0 1) ⟨0, hK0⟩ (fun y => y ^ 2 / 2) hconv id
    (fun y _ => hR y) 1 one_pos _ _ _ hRun (fun _ => 0) hnsq 1 0 hK0
  simp only [RegretT, Finset.sum_range_one, Finset.sum_const_zero, mul_zero, zero_add] at this
  have hbdd : BddBelow (Set.range fun y : ℝ => ⨅ (_ : y ∈ Set.Icc (0:ℝ) 1), -y ^ 2) := by
    refine ⟨-1, ?_⟩
    rintro _ ⟨y, rfl⟩
    dsimp only
    by_cases hy : y ∈ Set.Icc (0:ℝ) 1
    · rw [ciInf_pos hy]; nlinarith [hy.1, hy.2]
    · rw [ciInf_neg hy]; simp
  have hle : (⨅ y ∈ Set.Icc (0:ℝ) 1, -y ^ 2) ≤ -1 := by
    refine (ciInf_le hbdd 1).trans ?_
    rw [ciInf_pos (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨zero_le_one, le_rfl⟩)]
    norm_num
  norm_num at this
  simp only [Set.mem_Icc] at hle
  linarith

end OnlineConvexOpt.Regularization

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (R : E → ℝ) (hRconv : ConvexOn ℝ K R) (gradR : E → E)
    (hgradR : ∀ x ∈ K, HasGradientAt R (gradR x) x)
    (η : ℝ) (hη : 0 < η) (f : ℕ → E → ℝ) (x grad : ℕ → E)
    (hRun : IsRFTLRun K R η f x grad)
    (nsq : ℕ → ℝ) (hnsq : ∀ t, IsLocalDualNormSq R gradR (x t) (x (t + 1)) (grad t) (nsq t))
    (T : ℕ) (u : E) (hu : u ∈ K),
    RegretT K f x T ≤
      2 * η * (∑ t ∈ Finset.range T, nsq t) + (R u - R (x 0)) / η) := OnlineConvexOpt.Regularization.rftl_counter
