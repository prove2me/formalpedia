-- Prove2me | solution 1 for TranscendenceTheory.finite_zeros_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T13:11:15.124064+00:00
-- url     : https://prove2.me/submissions/3852c754-1669-4c9c-b763-fb607e30e42e

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CanonicalDecomposition

noncomputable section

open Filter Metric Set ComplexConjugate
open scoped Topology


private lemma analytic_dslope {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (a : ℂ) :
    AnalyticOnNhd ℂ (dslope f a) univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  exact (Complex.differentiableOn_dslope (by simp : univ ∈ 𝓝 a)).2 hf.differentiableOn

private lemma factor_one_zero {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (a : ℂ) (n : ℕ) (hn : (n : ℕ∞) ≤ analyticOrderAt f a) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g univ ∧
      ∀ z, f z = (z - a) ^ n * g z := by
  induction n generalizing f with
  | zero => exact ⟨f, hf, by simp⟩
  | succ n ih =>
    have hfa : f a = 0 := apply_eq_zero_of_analyticOrderAt_ne_zero (by
      intro h
      simp [h] at hn)
    have hfac : f = fun z => (z - a) * dslope f a z := by
      ext z
      exact (sub_smul_dslope_of_zero hfa z).symm
    have hds := analytic_dslope hf a
    have horder : analyticOrderAt f a = 1 + analyticOrderAt (dslope f a) a := by
      conv_lhs => rw [hfac]
      exact (analyticOrderAt_mul (by fun_prop) (hds a trivial)).trans (by simp)
    have hn' : (n : ℕ∞) ≤ analyticOrderAt (dslope f a) a := by
      rw [horder] at hn
      simpa [Nat.cast_add, add_comm] using hn
    obtain ⟨g, hg, hfg⟩ := ih hds hn'
    refine ⟨g, hg, fun z => ?_⟩
    conv_lhs => rw [hfac]
    dsimp only
    rw [hfg, pow_succ]
    ring

private lemma factor_finite_zeros {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (s : Finset ℂ) (m : ℂ → ℕ)
    (hm : ∀ a ∈ s, (m a : ℕ∞) ≤ analyticOrderAt f a) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g univ ∧
      ∀ z, f z = (∏ a ∈ s, (z - a) ^ m a) * g z := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => exact ⟨f, hf, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨g, hg, hfg⟩ := factor_one_zero hf a (m a) (hm a (by simp))
    have hmg : ∀ b ∈ s, (m b : ℕ∞) ≤ analyticOrderAt g b := by
      intro b hb
      have hba : b ≠ a := by intro h; subst b; exact ha hb
      have horder : analyticOrderAt f b = analyticOrderAt g b := by
        rw [show f = fun z => (z - a) ^ m a * g z from funext hfg]
        change analyticOrderAt ((fun z => (z - a) ^ m a) * g) b = _
        rw [analyticOrderAt_mul (by fun_prop) (hg b trivial),
          (show AnalyticAt ℂ (fun z => (z - a) ^ m a) b by fun_prop).analyticOrderAt_eq_zero.2
            (pow_ne_zero _ (sub_ne_zero.mpr hba)), zero_add]
      rw [← horder]
      exact hm b (by simp [hb])
    obtain ⟨q, hq, hgq⟩ := ih hg hmg
    refine ⟨q, hq, fun z => ?_⟩
    rw [hfg, hgq, Finset.prod_insert ha]
    ring

private lemma inner_factor_bound {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {a z : ℂ} (ha : ‖a‖ ≤ r) (hz : ‖z‖ ≤ r) :
    ‖z - a‖ ≤ (2 * r / R) * ‖((R : ℂ) ^ 2 - conj a * z) / R‖ := by
  have hR : 0 < R := hr.trans hrR
  have hdist := norm_sub_le z a
  have hd : ‖z - a‖ ≤ 2 * r := by linarith
  have hident : ‖(R : ℂ) ^ 2 - conj a * z‖ ^ 2 =
      R ^ 2 * ‖z - a‖ ^ 2 + (R ^ 2 - ‖a‖ ^ 2) * (R ^ 2 - ‖z‖ ^ 2) := by
    simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, ← Complex.ofReal_pow]
    ring
  have ha2 : ‖a‖ ^ 2 ≤ r ^ 2 := sq_le_sq₀ (norm_nonneg a) hr.le |>.2 ha
  have hz2 : ‖z‖ ^ 2 ≤ r ^ 2 := sq_le_sq₀ (norm_nonneg z) hr.le |>.2 hz
  have hr2 : r ^ 2 ≤ R ^ 2 := sq_le_sq₀ hr.le hR.le |>.2 hrR.le
  have hlow : (R ^ 2 - r ^ 2) ^ 2 ≤
      (R ^ 2 - ‖a‖ ^ 2) * (R ^ 2 - ‖z‖ ^ 2) := by
    rw [sq]
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hd2 : ‖z - a‖ ^ 2 ≤ 4 * r ^ 2 := by nlinarith [norm_nonneg (z - a)]
  have hsq : ((R ^ 2 + r ^ 2) * ‖z - a‖) ^ 2 ≤
      (2 * r * ‖(R : ℂ) ^ 2 - conj a * z‖) ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hd2) (sq_nonneg (R ^ 2 - r ^ 2))
    have hq := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 4 * r ^ 2 by positivity)
    nlinarith [hident]
  have hsharp : (R ^ 2 + r ^ 2) * ‖z - a‖ ≤
      2 * r * ‖(R : ℂ) ^ 2 - conj a * z‖ :=
    (sq_le_sq₀ (by positivity) (by positivity)).1 hsq
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  rw [div_mul_div_comm]
  apply (le_div_iff₀ (mul_pos hR hR)).2
  nlinarith [mul_nonneg (sq_nonneg r) (norm_nonneg (z - a))]

private lemma boundary_factor_norm {R : ℝ} (hR : 0 < R) {a z : ℂ}
    (ha : ‖a‖ < R) (hz : ‖z‖ = R) :
    ‖((R : ℂ) ^ 2 - conj a * z) / R‖ = ‖z - a‖ := by
  have hza : z - a ≠ 0 := by intro h; have := sub_eq_zero.mp h; subst z; linarith
  have h := Complex.norm_canonicalFactor_eval_circle_eq_one
    (mem_ball_zero_iff.mpr ha) (mem_sphere_zero_iff_norm.mpr hz)
  rw [Complex.canonicalFactor_apply, norm_div, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at h
  have hnum := (div_eq_one_iff_eq (mul_ne_zero hR.ne' (norm_ne_zero_iff.mpr hza))).1 h
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, hnum]
  exact mul_div_cancel_left₀ _ hR.ne'

private lemma finite_zeros_norm_bound {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (s : Finset ℂ) (m : ℂ → ℕ)
    (hm : ∀ a ∈ s, (m a : ℕ∞) ≤ analyticOrderAt f a)
    {r R C : ℝ} (hr : 0 < r) (hrR : r < R)
    (hs : ∀ a ∈ s, ‖a‖ ≤ r)
    (hC : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ C * (2 * r / R) ^ (∑ a ∈ s, m a) := by
  classical
  have hR := hr.trans hrR
  obtain ⟨g, hg, hfg⟩ := factor_finite_zeros hf s m hm
  let G : ℂ → ℂ := fun w => (∏ a ∈ s,
    (((R : ℂ) ^ 2 - conj a * w) / R) ^ m a) * g w
  have hG : AnalyticOnNhd ℂ G univ := by
    intro w hw
    apply AnalyticAt.mul _ (hg w hw)
    exact s.analyticAt_fun_prod (fun a ha => by fun_prop)
  have hGC : ∀ w ∈ sphere (0 : ℂ) R, ‖G w‖ ≤ C := by
    intro w hw
    have heq : ‖G w‖ = ‖f w‖ := by
      rw [hfg]
      simp only [G, norm_mul, norm_prod, norm_pow]
      congr 1
      apply Finset.prod_congr rfl
      intro a ha
      rw [boundary_factor_norm hR ((hs a ha).trans_lt hrR)
        (mem_sphere_zero_iff_norm.mp hw)]
    exact heq.le.trans (hC w hw)
  have hGz : ‖G z‖ ≤ C := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) R)
      isBounded_ball (Differentiable.diffContOnCl (fun w => (hG w trivial).differentiableAt)) ?_ ?_
    · simpa [frontier_ball (0 : ℂ) hR.ne'] using hGC
    · rw [closure_ball _ hR.ne']
      exact mem_closedBall_zero_iff.mpr (hz.trans hrR.le)
  have hprod : (∏ a ∈ s, ‖z - a‖ ^ m a) ≤
      (2 * r / R) ^ (∑ a ∈ s, m a) *
        (∏ a ∈ s, ‖((R : ℂ) ^ 2 - conj a * z) / R‖ ^ m a) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro a ha
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (inner_factor_bound hr hrR (hs a ha) hz) _
  calc
    ‖f z‖ = (∏ a ∈ s, ‖z - a‖ ^ m a) * ‖g z‖ := by
      rw [hfg, norm_mul, norm_prod]; simp only [norm_pow]
    _ ≤ ((2 * r / R) ^ (∑ a ∈ s, m a) *
        (∏ a ∈ s, ‖((R : ℂ) ^ 2 - conj a * z) / R‖ ^ m a)) * ‖g z‖ :=
      mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ = ‖G z‖ * (2 * r / R) ^ (∑ a ∈ s, m a) := by
      simp only [G, norm_mul, norm_prod, norm_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hGz (by positivity)

/-- Finite vanishing jets give the Schwarz decay factor and all Cauchy derivative bounds. -/
theorem solution (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ) (s : Finset ℂ) (m : ℂ → ℕ)
    (hm : ∀ a ∈ s, ∀ j < m a, iteratedDeriv j f a = 0)
    (r R C : ℝ) (hr : 0 < r) (hrR : r < R)
    (hs : ∀ a ∈ s, ‖a‖ ≤ r)
    (hC : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ C) :
    (∀ z : ℂ, ‖z‖ ≤ r → ‖f z‖ ≤ C * (2 * r / R) ^ (∑ a ∈ s, m a)) ∧
    ∀ (w : ℂ) (ρ : ℝ), 0 < ρ → ‖w‖ + ρ ≤ r → ∀ n : ℕ,
      ‖iteratedDeriv n f w‖ ≤
        n.factorial * (C * (2 * r / R) ^ (∑ a ∈ s, m a)) / ρ ^ n := by
  have horder : ∀ a ∈ s, (m a : ℕ∞) ≤ analyticOrderAt f a := by
    intro a ha
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf a trivial)).2 (hm a ha)
  have hsmall := fun z hz => finite_zeros_norm_bound hf s m horder hr hrR hs hC (z := z) hz
  refine ⟨hsmall, ?_⟩
  intro w ρ hρ hw n
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hρ
    (Differentiable.diffContOnCl (fun w => (hf w trivial).differentiableAt))
  intro z hz
  apply hsmall
  have hdist : ‖z - w‖ = ρ := mem_sphere_iff_norm.mp hz
  calc
    ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by simpa using norm_add_le (z - w) w
    _ ≤ r := by linarith

