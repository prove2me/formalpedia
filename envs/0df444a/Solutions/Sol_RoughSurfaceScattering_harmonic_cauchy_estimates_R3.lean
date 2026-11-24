-- Prove2me | solution 1 for RoughSurfaceScattering.harmonic_cauchy_estimates_R3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T06:12:11.798914+00:00
-- url     : https://prove2.me/submissions/5ba23ffb-33a3-4d8f-ba72-b20342429c17
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_harmonic_smooth_R3
import Theorems.Thm_RoughSurfaceScattering_harmonic_iteratedFDeriv_R3
import Theorems.Thm_RoughSurfaceScattering_harmonic_gradient_estimate_R3

open MeasureTheory Metric Nat
open RoughSurfaceScattering

theorem solution (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (x : EuclideanSpace ℝ (Fin 3)) (hf : InnerProductSpace.HarmonicAt f x) :
    ∃ R > (0 : ℝ), ∃ M ρ : ℝ, 0 < ρ ∧ (∀ n : ℕ, ContDiffOn ℝ n f (Metric.ball x R)) ∧
      ∀ n : ℕ, ∀ y ∈ Metric.ball x R,
        ‖iteratedFDeriv ℝ n f y‖ ≤ M * (n.factorial : ℝ) / ρ ^ n := by
  -- `f` is harmonic on a ball `B(x, ε)`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (InnerProductSpace.isOpen_setOfPred_harmonicAt (f := f)) x hf
  set U := ball x ε with hUdef
  have hU : IsOpen U := isOpen_ball
  have hfU : InnerProductSpace.HarmonicOnNhd f U := fun y hy => hball hy
  have hsm := harmonic_smooth_R3 f U hU hfU
  have hDh := harmonic_iteratedFDeriv_R3 f U hU hfU
  -- a bound for `f` on the closed ball `B*` of radius `3ε/4`
  set Bs := closedBall x (3 * ε / 4) with hBs
  have hBsU : Bs ⊆ U := closedBall_subset_ball (by linarith)
  obtain ⟨K, hK⟩ := (isCompact_closedBall x (3 * ε / 4)).exists_bound_of_continuousOn
    (((hsm 0).continuousOn).mono hBsU)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK x (mem_closedBall_self (by positivity)))
  -- nested-ball induction: `‖Dⁿf(y)‖ ≤ K (3n/s)ⁿ` whenever `B(y, s) ⊆ B*`
  have key : ∀ n : ℕ, ∀ s : ℝ, 0 < s → ∀ y, closedBall y s ⊆ Bs →
      ‖iteratedFDeriv ℝ n f y‖ ≤ K * (3 * n / s) ^ n := by
    intro n
    induction n with
    | zero =>
      intro s hs y hy
      rw [norm_iteratedFDeriv_zero]
      simpa using hK y (hy (mem_closedBall_self hs.le))
    | succ n ih =>
      intro s hs y hy
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      set t := s / ((n : ℝ) + 1) with ht
      have htpos : 0 < t := by positivity
      have hts : t ≤ s := div_le_self hs.le (by linarith [n.cast_nonneg (α := ℝ)])
      have hyt : closedBall y t ⊆ U := (closedBall_subset_closedBall hts).trans (hy.trans hBsU)
      -- bound for `Dⁿf` on the small ball `B(y, t)`
      have hinner : ∀ w ∈ closedBall y t,
          ‖iteratedFDeriv ℝ n f w‖ ≤ K * (3 * ((n : ℝ) + 1) / s) ^ n := by
        intro w hw
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          rw [norm_iteratedFDeriv_zero]
          simpa using hK w (hy ((closedBall_subset_closedBall hts) hw))
        · have hnr : (0 : ℝ) < n := by exact_mod_cast hn
          set s' := s * n / ((n : ℝ) + 1) with hs'
          have hs'pos : 0 < s' := by positivity
          have hsub : closedBall w s' ⊆ Bs := by
            refine (closedBall_subset_closedBall' ?_).trans hy
            rw [mem_closedBall] at hw
            have : t + s' = s := by rw [ht, hs']; field_simp; ring
            linarith
          have := ih s' hs'pos w hsub
          have heq : 3 * (n : ℝ) / s' = 3 * ((n : ℝ) + 1) / s := by
            rw [hs']; field_simp
          rwa [heq] at this
      have hgrad := harmonic_gradient_estimate_R3 (iteratedFDeriv ℝ n f) U hU (hDh n) y t
        htpos hyt _ hinner
      rw [← norm_fderiv_iteratedFDeriv]
      refine hgrad.trans (le_of_eq ?_)
      have hs0 : s ≠ 0 := hs.ne'
      have h3 : 3 / t = 3 * ((n : ℝ) + 1) / s := by rw [ht]; field_simp
      rw [h3, pow_succ]
      push_cast
      ring
  -- conclusion with `R = ε/4`, `s = ε/2`, `ρ = s/(3e)`
  refine ⟨ε / 4, by positivity, K, ε / 2 / (3 * Real.exp 1), by positivity,
    fun n => (hsm n).mono (ball_subset_ball (by linarith)), fun n y hy => ?_⟩
  have hsub : closedBall y (ε / 2) ⊆ Bs := by
    refine closedBall_subset_closedBall' ?_
    rw [mem_ball] at hy
    linarith
  refine (key n (ε / 2) (by positivity) y hsub).trans ?_
  have hfact : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have hpow : (n : ℝ) ^ n ≤ Real.exp 1 ^ n * n ! := by
    have := Real.pow_div_factorial_le_exp (x := (n : ℝ)) (by positivity) n
    rw [div_le_iff₀ hfact, ← Real.exp_one_pow] at this
    linarith
  have hεpos : 0 < ε / 2 := by positivity
  calc K * (3 * n / (ε / 2)) ^ n = K * (n : ℝ) ^ n * (3 / (ε / 2)) ^ n := by
        rw [show 3 * (n : ℝ) / (ε / 2) = n * (3 / (ε / 2)) by ring, mul_pow]; ring
    _ ≤ K * (Real.exp 1 ^ n * n !) * (3 / (ε / 2)) ^ n := by gcongr
    _ = K * n ! / (ε / 2 / (3 * Real.exp 1)) ^ n := by
        rw [div_pow, div_pow, div_pow, mul_pow]
        field_simp
        have h2 : (2 : ℝ) ^ n * (ε / 2) ^ n = ε ^ n := by rw [← mul_pow]; congr 1; ring
        rw [mul_assoc, h2]
