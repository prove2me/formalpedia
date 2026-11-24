-- Prove2me | solution 2 for RoughSurfaceScattering.harmonic_cauchy_estimates_R3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T10:28:47.882985+00:00
-- url     : https://prove2.me/submissions/92a5665e-b24b-4535-8b78-cfa128f9ac78
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_harmonic_smooth_R3
import Theorems.Thm_RoughSurfaceScattering_harmonic_iteratedFDeriv_R3
import Theorems.Thm_RoughSurfaceScattering_harmonic_gradient_estimate_C_R3

open MeasureTheory Metric Nat
open RoughSurfaceScattering

/-- The scalar gradient estimate lifts to multilinear-map-valued harmonic functions. -/
lemma grad_multilinear (C : ℝ) (hC0 : 0 < C)
    (hC : ∀ (f : EuclideanSpace ℝ (Fin 3) → ℂ) (U : Set (EuclideanSpace ℝ (Fin 3))),
      IsOpen U → InnerProductSpace.HarmonicOnNhd f U →
      ∀ (z : EuclideanSpace ℝ (Fin 3)) (r : ℝ), 0 < r → Metric.closedBall z r ⊆ U →
      ∀ K : ℝ, (∀ w ∈ Metric.closedBall z r, ‖f w‖ ≤ K) →
        ‖fderiv ℝ f z‖ ≤ C / r * K)
    (n : ℕ)
    (g : EuclideanSpace ℝ (Fin 3) →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => EuclideanSpace ℝ (Fin 3)) ℂ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U)
    (hg : InnerProductSpace.HarmonicOnNhd g U) (z : EuclideanSpace ℝ (Fin 3)) (r : ℝ)
    (hr : 0 < r) (hzr : closedBall z r ⊆ U) (K : ℝ)
    (hK : ∀ w ∈ closedBall z r, ‖g w‖ ≤ K) :
    ‖fderiv ℝ g z‖ ≤ C / r * K := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK z (mem_closedBall_self hr.le))
  have hdiff : DifferentiableAt ℝ g z :=
    (hg z (hzr (mem_closedBall_self hr.le))).1.differentiableAt (by norm_num)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  set A := ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => EuclideanSpace ℝ (Fin 3)) ℂ m
  have hA : fderiv ℝ (A ∘ g) z = A.comp (fderiv ℝ g z) :=
    (A.hasFDerivAt.comp z hdiff.hasFDerivAt).fderiv
  have hbound : ∀ w ∈ closedBall z r, ‖(A ∘ g) w‖ ≤ K * ∏ i, ‖m i‖ := by
    intro w hw
    calc ‖(A ∘ g) w‖ = ‖g w m‖ := rfl
      _ ≤ ‖g w‖ * ∏ i, ‖m i‖ := (g w).le_opNorm m
      _ ≤ K * ∏ i, ‖m i‖ := mul_le_mul_of_nonneg_right (hK w hw) (by positivity)
  have hest := hC (A ∘ g) U hU (hg.comp_CLM A) z r hr hzr _ hbound
  calc ‖fderiv ℝ g z v m‖ = ‖fderiv ℝ (A ∘ g) z v‖ := by rw [hA]; rfl
    _ ≤ ‖fderiv ℝ (A ∘ g) z‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C / r * (K * ∏ i, ‖m i‖) * ‖v‖ := mul_le_mul_of_nonneg_right hest (norm_nonneg _)
    _ = C / r * K * ‖v‖ * ∏ i, ‖m i‖ := by ring

theorem solution (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (x : EuclideanSpace ℝ (Fin 3)) (hf : InnerProductSpace.HarmonicAt f x) :
    ∃ R > (0 : ℝ), ∃ M ρ : ℝ, 0 < ρ ∧ (∀ n : ℕ, ContDiffOn ℝ n f (Metric.ball x R)) ∧
      ∀ n : ℕ, ∀ y ∈ Metric.ball x R,
        ‖iteratedFDeriv ℝ n f y‖ ≤ M * (n.factorial : ℝ) / ρ ^ n := by
  obtain ⟨C, hC0, hC⟩ := harmonic_gradient_estimate_C_R3
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
      ‖iteratedFDeriv ℝ n f y‖ ≤ K * (C * n / s) ^ n := by
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
          ‖iteratedFDeriv ℝ n f w‖ ≤ K * (C * ((n : ℝ) + 1) / s) ^ n := by
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
          have heq : C * (n : ℝ) / s' = C * ((n : ℝ) + 1) / s := by
            rw [hs']; field_simp
          rwa [heq] at this
      have hgrad := grad_multilinear C hC0 hC n (iteratedFDeriv ℝ n f) U hU (hDh n) y t
        htpos hyt _ hinner
      rw [← norm_fderiv_iteratedFDeriv]
      refine hgrad.trans (le_of_eq ?_)
      have hs0 : s ≠ 0 := hs.ne'
      have h3 : C / t = C * ((n : ℝ) + 1) / s := by rw [ht]; field_simp
      rw [h3, pow_succ]
      push_cast
      ring
  -- conclusion with `R = ε/4`, `s = ε/2`, `ρ = s/(3e)`
  refine ⟨ε / 4, by positivity, K, ε / 2 / (C * Real.exp 1), by positivity,
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
  calc K * (C * n / (ε / 2)) ^ n = K * (n : ℝ) ^ n * (C / (ε / 2)) ^ n := by
        rw [show C * (n : ℝ) / (ε / 2) = n * (C / (ε / 2)) by ring, mul_pow]; ring
    _ ≤ K * (Real.exp 1 ^ n * n !) * (C / (ε / 2)) ^ n := by gcongr
    _ = K * n ! / (ε / 2 / (C * Real.exp 1)) ^ n := by
        rw [div_pow, div_pow, div_pow, mul_pow]
        field_simp
        have h2 : (2 : ℝ) ^ n * (ε / 2) ^ n = ε ^ n := by rw [← mul_pow]; congr 1; ring
        rw [mul_assoc, h2]
