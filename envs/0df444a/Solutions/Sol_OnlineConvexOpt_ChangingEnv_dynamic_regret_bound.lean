-- Prove2me | solution 1 for OnlineConvexOpt.ChangingEnv.dynamic_regret_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T15:01:38.978032+00:00
-- url     : https://prove2.me/submissions/ae11a1d4-7a8c-48a9-963e-769516a4f114

import Mathlib
import Definitions.Def_OnlineConvexOpt_ChangingEnv_Regret
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

/-! Disproof of 27b69c5f `OnlineConvexOpt.ChangingEnv.dynamic_regret_bound`.

The bound `(3D²/(2η)) · P + (η/2) G² T` with `P = ∑ ‖u_t - u_{t+1}‖ + 1` mixes a length (the
path sum) with the dimensionless `+1`, so it fails once the diameter `D` is small. Take `E = ℝ`,
`K = [0, D]` with `D = η = 1/100`, `G = 1`, `f_t(z) = (-1)^t z`. OGD started at `x_0 = D`
alternates `D, 0, D, 0, …` (every gradient step lands in `K`), while the comparator
`u_t = D (1 - (-1)^t)/2` alternates `0, D, 0, D, …`. At `T = 4` the dynamic regret is
`4D = 1/25`, but the right-hand side is `(3D/2)(3D + 1) + 2D = 0.03545 < 0.04`. -/

set_option autoImplicit false

theorem drb_dp_hasDeriv (c y : ℝ) : HasDerivAt (fun z : ℝ => c * z) c y := by
  simpa using (hasDerivAt_id y).const_mul c

theorem drb_dp_hasGrad (c y : ℝ) : HasGradientAt (fun z : ℝ => c * z) c y :=
  (drb_dp_hasDeriv c y).hasGradientAt'

theorem drb_dp_grad_unique (c y v : ℝ) (h : HasGradientAt (fun z : ℝ => c * z) v y) :
    v = c := by
  exact h.hasDerivAt'.unique (drb_dp_hasDeriv c y)

theorem drb_dp_sign (t : ℕ) : (-1 : ℝ) ^ t = 1 ∨ (-1 : ℝ) ^ t = -1 := neg_one_pow_eq_or ℝ t

theorem drb_dp_mem_x (t : ℕ) :
    (1 / 100 : ℝ) * (1 + (-1) ^ t) / 2 ∈ Set.Icc (0 : ℝ) (1 / 100) := by
  rcases drb_dp_sign t with h | h <;> rw [h] <;> constructor <;> norm_num

theorem drb_dp_mem_u (t : ℕ) :
    (1 / 100 : ℝ) * (1 - (-1) ^ t) / 2 ∈ Set.Icc (0 : ℝ) (1 / 100) := by
  rcases drb_dp_sign t with h | h <;> rw [h] <;> constructor <;> norm_num

theorem drb_dp_step (t : ℕ) :
    (1 / 100 : ℝ) * (1 + (-1) ^ t) / 2 - (1 / 100 : ℝ) • ((-1 : ℝ) ^ t) =
      (1 / 100 : ℝ) * (1 + (-1) ^ (t + 1)) / 2 := by
  rw [pow_succ, smul_eq_mul]
  ring

open OnlineConvexOpt.ChangingEnv OnlineConvexOpt.FirstOrder in
theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D G : ℝ) (hDpos : 0 < D) (hGpos : 0 < G) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (f : ℕ → E → ℝ) (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (hfG : ∀ t, ∀ x ∈ K, ∀ v, HasGradientAt (f t) v x → ‖v‖ ≤ G)
    (η : ℝ) (hηpos : 0 < η)
    (u : ℕ → E) (hu : ∀ t, u t ∈ K)
    (x g : ℕ → E) (hOGD : IsOnlineGradientDescent K f (fun _ => η) x g)
    (T : ℕ) (hT : 1 ≤ T),
    DynamicRegretT f x u T ≤
      (3 * D ^ 2 / (2 * η)) * PathLength u T + (η / 2) * G ^ 2 * T) := by
  intro H
  have key := H (E := ℝ) (Set.Icc (0 : ℝ) (1 / 100)) (convex_Icc _ _)
    ⟨0, by constructor <;> norm_num⟩ (1 / 100) 1 (by norm_num) one_pos
    (by
      intro a ha b hb
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2])
    (fun t z => (-1 : ℝ) ^ t * z)
    (by
      intro t
      refine ⟨convex_Icc _ _, ?_⟩
      intro a _ b _ p q _ _ _
      exact le_of_eq (by simp only [smul_eq_mul]; ring))
    (by
      intro t z _ v hv
      rw [drb_dp_grad_unique _ _ _ hv]
      rcases drb_dp_sign t with h | h <;> rw [h] <;> norm_num)
    (1 / 100) (by norm_num)
    (fun t => (1 / 100 : ℝ) * (1 - (-1) ^ t) / 2) drb_dp_mem_u
    (fun t => (1 / 100 : ℝ) * (1 + (-1) ^ t) / 2) (fun t => (-1 : ℝ) ^ t)
    (by
      refine ⟨by simpa using drb_dp_mem_x 0, fun t => ⟨drb_dp_hasGrad _ _, ?_⟩⟩
      refine ⟨drb_dp_mem_x (t + 1), fun z _ => ?_⟩
      show dist ((1 / 100 : ℝ) * (1 + (-1) ^ t) / 2 - (1 / 100 : ℝ) • ((-1 : ℝ) ^ t))
          ((1 / 100 : ℝ) * (1 + (-1) ^ (t + 1)) / 2) ≤ _
      rw [drb_dp_step, dist_self]
      exact dist_nonneg)
    4 (by norm_num)
  unfold DynamicRegretT PathLength at key
  norm_num [Finset.sum_range_succ] at key
