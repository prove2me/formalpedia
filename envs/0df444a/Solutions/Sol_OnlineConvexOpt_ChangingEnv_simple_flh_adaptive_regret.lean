-- Prove2me | solution 1 for OnlineConvexOpt.ChangingEnv.simple_flh_adaptive_regret
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T12:32:22.797731+00:00
-- url     : https://prove2.me/submissions/9d2b5cae-e9bb-48fc-b2c5-90fede0e98c3

import Mathlib
import Definitions.Def_OnlineConvexOpt_ChangingEnv_Regret
import Definitions.Def_OnlineConvexOpt_ChangingEnv_FixedShare
import Definitions.Def_OnlineConvexOpt_ChangingEnv_ExpConcave

/-! Disproof of 862221eb `OnlineConvexOpt.ChangingEnv.simple_flh_adaptive_regret`.

`AdaptiveRegretT` is `⨆ r ∈ Finset.range T, ⨆ s ∈ Finset.Icc r (T-1), IntervalRegret …`. Over
`ℝ` this is `⨆ r, ⨆ (_ : r ∈ range T), …`, and for `r ∉ range T` the inner supremum is over an
empty index, which `Real` evaluates to `sSup ∅ = 0`. So `AdaptiveRegretT ≥ 0` always, even when
every interval regret is negative. Take `E = ℝ`, `K = ∅` (so `⨅ y ∈ K, _ = 0`), `α = 1`,
`f t ≡ -10` (exp-concave: `exp(10)` is constant), `T = 1`, `RegretBoundA = -10`, all experts at
`0`, `p = phat ≡ 1`, `x ≡ 0`. Every hypothesis holds, but the right side is
`-10 + log 2 + 1 < 0 ≤ AdaptiveRegretT`. -/

set_option autoImplicit false

theorem flh_dp_biInf_empty (g : ℝ → ℝ) : (⨅ y ∈ (∅ : Set ℝ), g y) = 0 := by
  have h : ∀ y : ℝ, (⨅ (_ : y ∈ (∅ : Set ℝ)), g y) = 0 := by
    intro y
    rw [ciInf_neg (by simp), Real.sInf_empty]
  simp only [h, ciInf_const]

open OnlineConvexOpt.ChangingEnv in
theorem flh_dp_adaptive_nonneg (K : Set ℝ) (f : ℕ → ℝ → ℝ) (x : ℕ → ℝ) (T : ℕ) :
    0 ≤ AdaptiveRegretT K f x T := by
  unfold AdaptiveRegretT
  refine Real.iSup_nonneg' ⟨T, ?_⟩
  rw [ciSup_neg (by simp), Real.sSup_empty]

open OnlineConvexOpt.ChangingEnv in
theorem flh_dp_run :
    IsFixedShareRun (fun (_ : ℕ) (_ : ℝ) => (-10 : ℝ)) 1 (1 / (2 * ((1 : ℕ) : ℝ)))
      (fun (_ : ℕ) (_ : Fin 1) => (0 : ℝ)) (fun _ _ => 1) (fun _ _ => 1) (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simp
  · intro t
    simp
  · intro t i
    simp only [Fin.sum_univ_one, one_mul]
    rw [div_self (Real.exp_ne_zero _)]
  · intro t i
    norm_num

open OnlineConvexOpt.ChangingEnv in
theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (α : ℝ) (hαpos : 0 < α)
    (f : ℕ → E → ℝ) (hfexp : ∀ t, IsAlphaExpConcaveOn Set.univ (f t) α)
    (RegretBoundA : ℝ)
    (T : ℕ) (hT : 1 ≤ T)
    (xi : ℕ → Fin T → E)
    (hxi : ∀ (i : Fin T) (r s : ℕ), (i : ℕ) ≤ r → r ≤ s → s < T →
      (∑ t ∈ Finset.Icc r s, f t (xi t i)) - ⨅ y ∈ K, ∑ t ∈ Finset.Icc r s, f t y ≤
        RegretBoundA)
    (p phat : ℕ → Fin T → ℝ) (x : ℕ → E)
    (hrun : IsFixedShareRun f α (1 / (2 * T)) xi p phat x),
    AdaptiveRegretT K f x T ≤
      RegretBoundA + (1 / α) * Real.log (2 * (T : ℝ) ^ 2) + 1 / α) := by
  intro H
  have key := H (E := ℝ) (∅ : Set ℝ) 1 one_pos (fun _ _ => -10)
    (by
      intro t
      show ConcaveOn ℝ Set.univ (fun _ => Real.exp (-1 * (-10 : ℝ)))
      exact concaveOn_const _ convex_univ)
    (-10) 1 le_rfl (fun _ _ => 0)
    (by
      intro i r s hir hrs hs
      have hr : r = 0 := by omega
      have hs0 : s = 0 := by omega
      subst hr hs0
      rw [flh_dp_biInf_empty]
      simp)
    (fun _ _ => 1) (fun _ _ => 1) (fun _ => 0) flh_dp_run
  have h0 := flh_dp_adaptive_nonneg (∅ : Set ℝ) (fun _ _ => -10) (fun _ => 0) 1
  have hlog : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
  have hR : -10 + (1 / (1 : ℝ)) * Real.log (2 * ((1 : ℕ) : ℝ) ^ 2) + 1 / (1 : ℝ) < 0 := by
    rw [Nat.cast_one, one_pow, mul_one, div_one, one_mul]
    linarith
  linarith
