-- Prove2me | solution 1 for Rudin.ch05_taylor_helper
-- status  : ACCEPTED   (disprove)
-- author  : @Lucas
-- created : 2026-09-13T15:00:59.31368+00:00
-- url     : https://prove2.me/submissions/0e597ada-1161-497f-8fc2-8509d85ae698

import Mathlib

open Filter Topology Set

/-- The formal statement of Taylor's theorem with Lagrange remainder is false in Mathlib:
`iteratedDeriv` (like `deriv`) is defined to be `0` at points of non-differentiability, so the
hypotheses do not force `f` itself to be continuous or to actually possess lower-order
derivatives. The spike `f = 1_{{1}}` is a counter-example. -/
theorem solution :
    ¬ (∀ (a b : ℝ) (_hab : a < b) (f : ℝ → ℝ) (n : ℕ) (_hn : 0 < n)
        (_hcont : ContinuousOn (iteratedDeriv (n - 1) f) (Set.Icc a b))
        (_hderiv : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ (iteratedDeriv (n - 1) f) t)
        (α β : ℝ) (_hα : α ∈ Set.Icc a b) (_hβ : β ∈ Set.Icc a b) (_hne : α ≠ β),
        ∃ x : ℝ, ((α < x ∧ x < β) ∨ (β < x ∧ x < α)) ∧
          f β = (∑ k ∈ Finset.range n, iteratedDeriv k f α / (k.factorial : ℝ) * (β - α) ^ k)
            + iteratedDeriv n f x / (n.factorial : ℝ) * (β - α) ^ n) := by
  intro H
  -- Spike at `1`: value `1` at `1`, value `0` elsewhere.
  let f : ℝ → ℝ := fun x => if x = 1 then 1 else 0
  have hf1 : f 1 = 1 := if_pos rfl
  have hf_ne : ∀ x, x ≠ 1 → f x = 0 := fun x hx => if_neg hx
  -- `f` is not continuous at `1`, hence not differentiable there.
  have hnot : ¬ DifferentiableAt ℝ f 1 := by
    intro hd
    have hc : ContinuousAt f 1 := hd.continuousAt
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ, hδpos, hδ⟩ := hc (1 / 2) (by norm_num)
    have hpos : 0 < δ / 2 := half_pos hδpos
    have hne : (1 + δ / 2 : ℝ) ≠ 1 := by linarith
    have hdist : dist (1 + δ / 2) (1 : ℝ) < δ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hpos]
      linarith
    have hlt := hδ hdist
    have hfpt : f (1 + δ / 2) = 0 := if_neg hne
    rw [hfpt, hf1, Real.dist_eq, zero_sub, abs_neg, abs_one] at hlt
    linarith
  -- Consequently `deriv f` vanishes everywhere.
  have hderiv0 : deriv f = fun _ => 0 := by
    funext x
    by_cases hx : x = 1
    · subst hx
      exact deriv_zero_of_not_differentiableAt hnot
    · have hloc : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [eventually_ne_nhds hx] with y hy
        exact if_neg hy
      exact (hloc.deriv_eq).trans (deriv_const x 0)
  have hiter1 : iteratedDeriv 1 f = fun _ => 0 := by
    rw [iteratedDeriv_one, hderiv0]
  have hiter2 : iteratedDeriv 2 f = fun _ => 0 := by
    funext x
    rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, hiter1, deriv_const]
  -- The Taylor hypotheses hold vacuously for `n = 2` on `[0, 1]`.
  have hab : (0 : ℝ) < 1 := by norm_num
  have hn : (0 : ℕ) < 2 := by decide
  have hcont : ContinuousOn (iteratedDeriv (2 - 1) f) (Icc (0 : ℝ) 1) := by
    change ContinuousOn (iteratedDeriv 1 f) _
    rw [hiter1]
    exact continuousOn_const
  have hdiff : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ (iteratedDeriv (2 - 1) f) t := by
    intro t _ht
    change DifferentiableAt ℝ (iteratedDeriv 1 f) t
    rw [hiter1]
    exact differentiableAt_const 0
  have hα : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hβ : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hne01 : (0 : ℝ) ≠ 1 := zero_ne_one
  obtain ⟨x, _hxbtw, hxeq⟩ := H 0 1 hab f 2 hn hcont hdiff 0 1 hα hβ hne01
  -- The Lagrange identity collapses to `1 = 0`.
  have hsum0 :
      (∑ k ∈ Finset.range 2, iteratedDeriv k f 0 / (k.factorial : ℝ) * ((1 : ℝ) - 0) ^ k) = 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [iteratedDeriv_zero, iteratedDeriv_one, hderiv0, hf_ne]
  have hrem0 :
      iteratedDeriv 2 f x / ((2 : ℕ).factorial : ℝ) * ((1 : ℝ) - 0) ^ 2 = 0 := by
    simp [hiter2]
  have : f 1 = (0 : ℝ) := by
    calc
      f 1 = (∑ k ∈ Finset.range 2,
                iteratedDeriv k f 0 / (k.factorial : ℝ) * ((1 : ℝ) - 0) ^ k) +
              iteratedDeriv 2 f x / ((2 : ℕ).factorial : ℝ) * ((1 : ℝ) - 0) ^ 2 := hxeq
      _ = 0 + 0 := by rw [hsum0, hrem0]
      _ = 0 := zero_add 0
  rw [hf1] at this
  exact one_ne_zero this
