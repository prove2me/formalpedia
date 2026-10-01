-- Prove2me | solution 1 for OnlineConvexOpt.ProjectionFree.ocg_iterate_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T17:44:34.466974+00:00
-- url     : https://prove2.me/submissions/8f519214-da76-465a-8e8c-fbc80e8710e9

import Mathlib
import Definitions.Def_OnlineConvexOpt_ProjectionFree_AggregateFunction

/-! Disproof of `OnlineConvexOpt.ProjectionFree.ocg_iterate_bound`.

Counterexample: `E = ℝ`, `K = [0,1]`, `D = G = T = 1` (so `η = 1/2`), `x₁ = 0`,
`σ t = min 1 (2/√t)`, linear costs `f τ y = g τ * y` with `g τ = -1` at `τ = 4224` and `0`
otherwise. Every oracle call before round 4225 sees a zero gradient, the tie is broken
toward `0`, so `x 4225 = 0`. But `F_4225 y = -y/2 + y²` has minimiser `1/4`, so
`h_4225 = 1/16 > 4/65 = 2 D² σ_4225`. -/

namespace Cex4aa8a100

open OnlineConvexOpt.ProjectionFree

/-- cost gradients: a single `-1` at round 4224 -/
noncomputable def gcex (τ : ℕ) : ℝ := if τ = 4224 then -1 else 0

/-- step sizes `σ t = min 1 (2/√t)` -/
noncomputable def σcex (t : ℕ) : ℝ := min 1 (2 / Real.sqrt t)

/-- linear-minimisation oracle over `[0,1]`, ties broken toward `0` -/
noncomputable def vcex (n : ℕ) (y : ℝ) : ℝ :=
  if 0 ≤ AggregateGradient gcex (0 : ℝ) (1 / 2) n y then 0 else 1

/-- the iterates -/
noncomputable def xcex : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 - σcex n) * xcex n + σcex n * vcex n (xcex n)

theorem sum_gcex (t : ℕ) :
    ∑ τ ∈ Finset.Ico 1 t, gcex τ = if 4224 < t then -1 else 0 := by
  unfold gcex
  rw [Finset.sum_ite_eq']
  by_cases h : 4224 < t
  · rw [if_pos (by rw [Finset.mem_Ico]; omega), if_pos h]
  · rw [if_neg (by rw [Finset.mem_Ico]; omega), if_neg h]

theorem agg_eq (t : ℕ) (y : ℝ) :
    AggregateFunction gcex (0 : ℝ) (1 / 2) t y =
      1 / 2 * ((if 4224 < t then (-1 : ℝ) else 0) * y) + y ^ 2 := by
  unfold AggregateFunction
  simp only [Real.inner_apply, sub_zero, Real.norm_eq_abs, sq_abs]
  rw [← Finset.sum_mul, sum_gcex]

theorem xcex_zero : ∀ n, n ≤ 4225 → xcex n = 0 := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hx : xcex n = 0 := ih (by omega)
    have hv : vcex n (xcex n) = 0 := by
      unfold vcex AggregateGradient
      rw [hx, sum_gcex, if_neg (show ¬ (4224 < n) by omega)]
      simp
    show (1 - σcex n) * xcex n + σcex n * vcex n (xcex n) = 0
    rw [hv, hx]; ring

end Cex4aa8a100

open OnlineConvexOpt.ProjectionFree in
theorem solution : ¬ (∀
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (G : ℝ) (hGpos : 0 < G)
    (f : ℕ → E → ℝ) (hfG : ∀ t, ∀ x ∈ K, ∀ y ∈ K, |f t x - f t y| ≤ G * dist x y)
    (gradf : ℕ → E) (x1 : E) (hx1 : x1 ∈ K)
    (T : ℕ) (hT : 1 ≤ T)
    (η : ℝ) (hη : η = D / (2 * G * (T : ℝ) ^ (3 / 4 : ℝ)))
    (σ : ℕ → ℝ) (hσ : ∀ t : ℕ, 1 ≤ t → σ t = min 1 (2 / Real.sqrt t))
    (x v : ℕ → E) (hrun : IsOnlineConditionalGradientRun K f gradf x1 η σ x v)
    (xstar : ℕ → E)
    (hxstar : ∀ t : ℕ, 1 ≤ t → xstar t ∈ K ∧
      ∀ y ∈ K, AggregateFunction gradf x1 η t (xstar t) ≤ AggregateFunction gradf x1 η t y)
    (t : ℕ) (ht : 1 ≤ t),
    AggregateFunction gradf x1 η t (x t) - AggregateFunction gradf x1 η t (xstar t) ≤
      2 * D ^ 2 * σ t) := by
  open Cex4aa8a100 in
  intro h
  have hD : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, dist x y ≤ 1 := by
    intro x hx y hy
    rw [Real.dist_eq, abs_sub_le_iff]
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    constructor <;> linarith
  have hfG : ∀ t, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |(fun y : ℝ => gcex t * y) x - (fun y : ℝ => gcex t * y) y| ≤ 1 * dist x y := by
    intro t x _ y _
    simp only
    rw [← mul_sub, abs_mul, Real.dist_eq, one_mul]
    have hg : |gcex t| ≤ 1 := by
      unfold gcex; split_ifs <;> norm_num
    exact mul_le_of_le_one_left (abs_nonneg _) hg
  have hη : (1 / 2 : ℝ) = 1 / (2 * 1 * ((1 : ℕ) : ℝ) ^ (3 / 4 : ℝ)) := by
    simp
  have hrun : IsOnlineConditionalGradientRun (Set.Icc (0 : ℝ) 1)
      (fun t (y : ℝ) => gcex t * y) gcex 0 (1 / 2) σcex xcex
      (fun n => vcex n (xcex n)) := by
    refine ⟨xcex_zero 1 (by norm_num), ⟨le_rfl, zero_le_one⟩, ?_, ?_, ?_⟩
    · intro t _
      have hd : HasDerivAt (fun y : ℝ => gcex t * y) (gcex t) (xcex t) := by
        simpa using (hasDerivAt_id (xcex t)).const_mul (gcex t)
      exact hd.hasGradientAt'
    · intro t _
      show IsLinearMinimizer _ _ (vcex t (xcex t))
      unfold vcex
      split_ifs with hc
      · refine ⟨⟨le_rfl, zero_le_one⟩, fun y hy => ?_⟩
        rw [Real.inner_apply, Real.inner_apply, mul_zero]
        exact mul_nonneg hc hy.1
      · refine ⟨⟨zero_le_one, le_rfl⟩, fun y hy => ?_⟩
        rw [Real.inner_apply, Real.inner_apply, mul_one]
        have hc' : AggregateGradient gcex (0 : ℝ) (1 / 2) t (xcex t) < 0 := lt_of_not_ge hc
        nlinarith [hy.2]
    · intro t _
      simp only [smul_eq_mul]
      rfl
  have hxstar : ∀ t : ℕ, 1 ≤ t →
      (fun t : ℕ => if 4224 < t then (1 / 4 : ℝ) else 0) t ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        AggregateFunction gcex (0 : ℝ) (1 / 2) t
          ((fun t : ℕ => if 4224 < t then (1 / 4 : ℝ) else 0) t) ≤
        AggregateFunction gcex (0 : ℝ) (1 / 2) t y := by
    intro t _
    simp only
    by_cases ht : 4224 < t
    · rw [if_pos ht]
      refine ⟨⟨by norm_num, by norm_num⟩, fun y _ => ?_⟩
      rw [agg_eq, agg_eq, if_pos ht]
      nlinarith [sq_nonneg (y - 1 / 4)]
    · rw [if_neg ht]
      refine ⟨⟨le_rfl, zero_le_one⟩, fun y _ => ?_⟩
      rw [agg_eq, agg_eq, if_neg ht]
      nlinarith [sq_nonneg y]
  have key := h (Set.Icc (0 : ℝ) 1) (convex_Icc 0 1) ⟨0, le_rfl, zero_le_one⟩ 1 one_pos hD
    1 one_pos (fun t (y : ℝ) => gcex t * y) hfG gcex 0 ⟨le_rfl, zero_le_one⟩ 1 le_rfl
    (1 / 2) hη σcex (fun t _ => rfl) xcex (fun n => vcex n (xcex n)) hrun
    (fun t : ℕ => if 4224 < t then (1 / 4 : ℝ) else 0) hxstar 4225 (by norm_num)
  rw [xcex_zero 4225 le_rfl, if_pos (show 4224 < 4225 by norm_num), agg_eq, agg_eq,
    if_pos (show 4224 < 4225 by norm_num)] at key
  have hs : σcex 4225 = 2 / 65 := by
    unfold σcex
    have : Real.sqrt ((4225 : ℕ) : ℝ) = 65 := by
      rw [show ((4225 : ℕ) : ℝ) = (65 : ℝ) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [this]
    norm_num
  rw [hs] at key
  norm_num at key
