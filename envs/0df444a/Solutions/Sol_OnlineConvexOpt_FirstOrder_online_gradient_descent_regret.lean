-- Prove2me | solution 1 for OnlineConvexOpt.FirstOrder.online_gradient_descent_regret
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T07:40:19.149973+00:00
-- url     : https://prove2.me/submissions/ceda9c47-6b77-4e96-87e2-023c64c4b667

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

/-! Disproof of d2671c40 `OnlineConvexOpt.FirstOrder.online_gradient_descent_regret`.

`RegretT K f x T` subtracts `⨅ y ∈ K, ∑ t ∈ range T, f t y`. Over `ℝ` this is
`⨅ y, ⨅ (_ : y ∈ K), …`, and for `y ∉ K` the inner infimum is over an empty index, which
`Real` evaluates to `sInf ∅ = 0`. So whenever `K ≠ univ` the "comparator" term is at most `0`,
and positive constant costs make the regret equal to the total cost. Take `E = ℝ`, `K = {0}`,
`D = G = 1`, `f t ≡ 2`, `x ≡ 0`, `g ≡ 0`, `T = 1`: every hypothesis holds, but
`RegretT = 2 - (⨅ …) ≥ 2 > 3/2 = (3/2)·G·D·√1`. -/

set_option autoImplicit false

theorem oco_dp_iInf_singleton_nonpos (c : ℝ) :
    (⨅ y ∈ ({0} : Set ℝ), c) ≤ 0 := by
  refine Real.iInf_nonpos' ⟨1, ?_⟩
  have h1 : (1 : ℝ) ∉ ({0} : Set ℝ) := by simp
  rw [ciInf_neg h1, Real.sInf_empty]

open OnlineConvexOpt.FirstOrder in
theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (K : Set E) (D G : ℝ) (f : ℕ → E → ℝ)
    (hKconv : Convex ℝ K) (hKcomplete : IsComplete K) (hKne : K.Nonempty)
    (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) (hGpos : 0 < G) (hDpos : 0 < D)
    (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (hG : ∀ t, ∀ x ∈ K, ∀ v, HasGradientAt (f t) v x → ‖v‖ ≤ G)
    (η : ℕ → ℝ) (hη : ∀ t : ℕ, η t = D / (G * Real.sqrt (t + 1)))
    (x g : ℕ → E) (hOGD : IsOnlineGradientDescent K f η x g)
    (T : ℕ) (hT : 1 ≤ T),
    RegretT K f x T ≤ (3 / 2) * G * D * Real.sqrt T) := by
  intro H
  have key := H (E := ℝ) ({0} : Set ℝ) 1 1 (fun _ _ => (2 : ℝ))
    (convex_singleton 0) isClosed_singleton.isComplete (Set.singleton_nonempty 0)
    (by
      intro a ha b hb
      rw [Set.mem_singleton_iff] at ha hb
      subst ha hb
      simp)
    one_pos one_pos
    (fun _ => convexOn_const 2 (convex_singleton 0))
    (by
      intro t a _ v hv
      have h0 : v = 0 := hv.unique (hasGradientAt_const a (2 : ℝ))
      rw [h0, norm_zero]
      exact zero_le_one)
    (fun t => 1 / (1 * Real.sqrt (t + 1))) (fun _ => rfl)
    (fun _ => 0) (fun _ => 0)
    (by
      refine ⟨rfl, fun t => ⟨hasGradientAt_const _ _, rfl, ?_⟩⟩
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact le_rfl)
    1 le_rfl
  have hinf := oco_dp_iInf_singleton_nonpos (∑ t ∈ Finset.range 1, (2 : ℝ))
  unfold RegretT at key
  simp only [Finset.sum_range_one, Nat.cast_one, Real.sqrt_one, mul_one] at key hinf
  linarith
