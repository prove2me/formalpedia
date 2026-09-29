-- Prove2me | solution 1 for OnlineConvexOpt.FirstOrder.online_gradient_descent_strongly_convex_regret
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T07:40:19.27798+00:00
-- url     : https://prove2.me/submissions/28db6119-2749-4fb2-9d03-db409b2e11b7

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

/-! Disproof of 05cad211 `OnlineConvexOpt.FirstOrder.online_gradient_descent_strongly_convex_regret`.

`RegretT K f x T` subtracts `⨅ y ∈ K, ∑ t ∈ range T, f t y`. Over `ℝ` this is
`⨅ y, ⨅ (_ : y ∈ K), …`, and for `y ∉ K` the inner infimum is over an empty index, which
`Real` evaluates to `sInf ∅ = 0`. So whenever `K ≠ univ` the comparator term is at most `0`,
and positive constant costs make the regret equal to the total cost. Take `E = ℝ`, `K = {0}`,
`G = α = 1`, `f t ≡ 2` (strongly convex on the singleton, where the defining inequality is
`2 ≤ 2`), `x ≡ 0`, `g ≡ 0`, `T = 1`. Every hypothesis holds, but
`RegretT ≥ 2 > 1/2 = (G²/(2α))·(1 + log 1)`. -/

set_option autoImplicit false

theorem oco_dp_iInf_singleton_nonpos (c : ℝ) :
    (⨅ y ∈ ({0} : Set ℝ), c) ≤ 0 := by
  refine Real.iInf_nonpos' ⟨1, ?_⟩
  have h1 : (1 : ℝ) ∉ ({0} : Set ℝ) := by simp
  rw [ciInf_neg h1, Real.sInf_empty]

theorem oco_dp_strongConvexOn_singleton (c m : ℝ) :
    StrongConvexOn ({0} : Set ℝ) m (fun _ => c) := by
  refine ⟨convex_singleton 0, ?_⟩
  intro a ha b hb s t _ _ hst
  rw [Set.mem_singleton_iff] at ha hb
  subst ha hb
  simp only [sub_self, norm_zero, smul_eq_mul]
  have : s * c + t * c = c := by rw [← add_mul, hst, one_mul]
  nlinarith

open OnlineConvexOpt.FirstOrder in
theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (K : Set E) (G : ℝ) (f : ℕ → E → ℝ)
    (hKconv : Convex ℝ K) (hKcomplete : IsComplete K) (hKne : K.Nonempty) (hGpos : 0 < G)
    (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (hG : ∀ t, ∀ x ∈ K, ∀ v, HasGradientAt (f t) v x → ‖v‖ ≤ G)
    (α : ℝ) (hα : 0 < α) (hfSC : ∀ t, StrongConvexOn K α (f t))
    (η : ℕ → ℝ) (hη : ∀ t : ℕ, η t = 1 / (α * (t + 1)))
    (x g : ℕ → E) (hOGD : IsOnlineGradientDescent K f η x g)
    (T : ℕ) (hT : 1 ≤ T),
    RegretT K f x T ≤ (G ^ 2 / (2 * α)) * (1 + Real.log T)) := by
  intro H
  have key := H (E := ℝ) ({0} : Set ℝ) 1 (fun _ _ => (2 : ℝ))
    (convex_singleton 0) isClosed_singleton.isComplete (Set.singleton_nonempty 0) one_pos
    (fun _ => convexOn_const 2 (convex_singleton 0))
    (by
      intro t a _ v hv
      have h0 : v = 0 := hv.unique (hasGradientAt_const a (2 : ℝ))
      rw [h0, norm_zero]
      exact zero_le_one)
    1 one_pos (fun _ => oco_dp_strongConvexOn_singleton 2 1)
    (fun t => 1 / (1 * ((t : ℝ) + 1))) (fun _ => rfl)
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
  simp only [Finset.sum_range_one, Nat.cast_one, Real.log_one, add_zero, mul_one,
    one_pow] at key hinf
  linarith
