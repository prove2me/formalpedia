-- Prove2me | solution 1 for PriceQualityService.Uniform.drdt
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:19:16.420676+00:00
-- url     : https://prove2.me/submissions/65ef9099-a2f9-41ed-b296-85c8e09de0d7

import Mathlib
import Definitions.Def_PriceQualityService_Uniform_Reduction

set_option autoImplicit false
open PriceQualityService.Uniform Finset Filter Topology

theorem gTerm_eq' {N : ℕ} (α a b c s : Fin N → ℝ) (r t : ℝ) (i : Fin N) :
    gTerm α a b c s r t i = Real.exp (exponent α a b c s t i) / Real.exp (1 + r) := by
  unfold gTerm
  rw [← Real.exp_sub]; congr 1; ring

theorem sum_gTerm' {N : ℕ} (α a b c s : Fin N → ℝ) (r t : ℝ) :
    ∑ i, gTerm α a b c s r t i = yTotal α a b c s t / Real.exp (1 + r) := by
  simp_rw [gTerm_eq']
  rw [← Finset.sum_div]; rfl

theorem yTotal_nonneg' {N : ℕ} (α a b c s : Fin N → ℝ) (t : ℝ) : 0 ≤ yTotal α a b c s t :=
  Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)

theorem exponent_hasDeriv' {N : ℕ} (α a b c s : Fin N → ℝ) (t : ℝ) (i : Fin N) :
    HasDerivAt (fun t => exponent α a b c s t i) (aTerm α a b c s t i) t := by
  have h1 : HasDerivAt (fun t : ℝ => b i ^ 2 * t ^ 2 / (4 * c i))
      (b i ^ 2 * (2 * t) / (4 * c i)) t := by
    have := ((hasDerivAt_pow 2 t).const_mul (b i ^ 2)).div_const (4 * c i)
    simpa using this
  have h2 : HasDerivAt (fun t : ℝ => (s i - a i + α i * b i / (2 * c i)) * t)
      (s i - a i + α i * b i / (2 * c i)) t := by
    simpa using (hasDerivAt_id t).const_mul (s i - a i + α i * b i / (2 * c i))
  have h3 := (h1.add h2).add_const (α i ^ 2 / (4 * c i))
  unfold exponent aTerm
  refine h3.congr_deriv ?_
  ring

theorem yTotal_hasDeriv' {N : ℕ} (α a b c s : Fin N → ℝ) (t : ℝ) :
    HasDerivAt (yTotal α a b c s)
      (∑ i, aTerm α a b c s t i * Real.exp (exponent α a b c s t i)) t := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      HasDerivAt (fun t => Real.exp (exponent α a b c s t i))
        (Real.exp (exponent α a b c s t i) * aTerm α a b c s t i) t :=
    fun i _ => (exponent_hasDeriv' α a b c s t i).exp
  have := HasDerivAt.fun_sum h
  unfold yTotal
  refine this.congr_deriv ?_
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem R_facts' {N : ℕ} (α a b c s : Fin N → ℝ) (R : ℝ → ℝ)
    (hR : ∀ t, R t = ∑ i, gTerm α a b c s (R t) t i) :
    (∀ t, 0 ≤ R t) ∧ (∀ t, R t * Real.exp (1 + R t) = yTotal α a b c s t) ∧
    ∀ t, ContinuousAt R t := by
  have hRy : ∀ t, R t = yTotal α a b c s t / Real.exp (1 + R t) := fun t => by
    rw [← sum_gTerm']; exact hR t
  have hR0 : ∀ t, 0 ≤ R t := fun t => by
    rw [hRy t]; exact div_nonneg (yTotal_nonneg' α a b c s t) (Real.exp_pos _).le
  have hΦy : ∀ t, R t * Real.exp (1 + R t) = yTotal α a b c s t := fun t =>
    ((eq_div_iff (Real.exp_pos _).ne').1 (hRy t))
  refine ⟨hR0, hΦy, ?_⟩
  have hmono : ∀ x y : ℝ, 0 ≤ x → x < y → x * Real.exp (1 + x) < y * Real.exp (1 + y) := by
    intro x y hx hxy
    have h1 : Real.exp (1 + x) ≤ Real.exp (1 + y) := Real.exp_le_exp.2 (by linarith)
    have h2 := Real.exp_pos (1 + y)
    calc x * Real.exp (1 + x) ≤ x * Real.exp (1 + y) := mul_le_mul_of_nonneg_left h1 hx
      _ < y * Real.exp (1 + y) := mul_lt_mul_of_pos_right hxy h2
  have hYc : Continuous (yTotal α a b c s) := by
    unfold yTotal exponent; fun_prop
  intro t0
  rw [ContinuousAt, tendsto_order]
  constructor
  · intro a' ha'
    by_cases h0 : a' < 0
    · exact Filter.Eventually.of_forall (fun t => lt_of_lt_of_le h0 (hR0 t))
    · push Not at h0
      have hlt : a' * Real.exp (1 + a') < yTotal α a b c s t0 := by
        rw [← hΦy t0]; exact hmono _ _ h0 ha'
      have hev : ∀ᶠ t in 𝓝 t0, a' * Real.exp (1 + a') < yTotal α a b c s t :=
        (hYc.continuousAt.eventually (lt_mem_nhds hlt))
      filter_upwards [hev] with t ht
      by_contra hcon
      push Not at hcon
      rcases hcon.lt_or_eq with h | h
      · have := hmono _ _ (hR0 t) h
        rw [hΦy t] at this; linarith
      · have := hΦy t
        rw [h] at this
        linarith
  · intro b' hb'
    have hlt : yTotal α a b c s t0 < b' * Real.exp (1 + b') := by
      rw [← hΦy t0]; exact hmono _ _ (hR0 t0) hb'
    have hev : ∀ᶠ t in 𝓝 t0, yTotal α a b c s t < b' * Real.exp (1 + b') :=
      (hYc.continuousAt.eventually (gt_mem_nhds hlt))
    filter_upwards [hev] with t ht
    by_contra hcon
    push Not at hcon
    rcases hcon.lt_or_eq with h | h
    · have := hmono _ _ (by linarith [hR0 t0, hb']) h
      rw [hΦy t] at this; linarith
    · have := hΦy t
      rw [← h] at this
      linarith

theorem drdt' {N : ℕ} (α a b c s : Fin N → ℝ) (R : ℝ → ℝ)
    (hR : ∀ t, R t = ∑ i, gTerm α a b c s (R t) t i) (t : ℝ) :
    HasDerivAt R
      ((∑ i, aTerm α a b c s t i * gTerm α a b c s (R t) t i)
        / (1 + ∑ i, gTerm α a b c s (R t) t i)) t := by
  obtain ⟨hR0, hΦy, hRc⟩ := R_facts' α a b c s R hR
  have hΦ : HasStrictDerivAt (fun r : ℝ => r * Real.exp (1 + r))
      ((1 + R t) * Real.exp (1 + R t)) (R t) := by
    have h := (hasStrictDerivAt_id (R t)).mul (((hasStrictDerivAt_id (R t)).const_add 1).exp)
    refine h.congr_deriv ?_
    simp only [id]; ring
  have hne : (1 + R t) * Real.exp (1 + R t) ≠ 0 := by
    have := hR0 t; positivity
  have hρ := hΦ.to_localInverse hne
  have hleft := hΦ.eventually_left_inverse hne
  set ρ := hΦ.localInverse _ _ _ hne with hρdef
  have hev : ∀ᶠ t' in 𝓝 t, R t' = ρ (yTotal α a b c s t') := by
    have := (hRc t).eventually hleft
    filter_upwards [this] with t' ht'
    rw [← hΦy t']
    exact ht'.symm
  have hY := yTotal_hasDeriv' α a b c s t
  have hρd : HasDerivAt ρ ((1 + R t) * Real.exp (1 + R t))⁻¹ (yTotal α a b c s t) := by
    have := hρ.hasDerivAt
    rwa [hΦy t] at this
  have hcomp := hρd.comp t hY
  have h2 := hcomp.congr_of_eventuallyEq hev
  refine h2.congr_deriv ?_
  have hG : ∀ i, gTerm α a b c s (R t) t i =
      Real.exp (exponent α a b c s t i) / Real.exp (1 + R t) := fun i => gTerm_eq' _ _ _ _ _ _ _ _
  have hsumG : ∑ i, gTerm α a b c s (R t) t i = R t := (hR t).symm
  rw [hsumG]
  simp_rw [hG, ← mul_div_assoc]
  rw [← Finset.sum_div]
  have h0 := hR0 t
  have h1 : (0:ℝ) < Real.exp (1 + R t) := Real.exp_pos _
  field_simp

theorem solution {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (R : ℝ → ℝ)
    (hR : ∀ t, R t = ∑ i, gTerm α a b c s (R t) t i) (t : ℝ) :
    HasDerivAt R
      ((∑ i, aTerm α a b c s t i * gTerm α a b c s (R t) t i)
        / (1 + ∑ i, gTerm α a b c s (R t) t i)) t := drdt' α a b c s R hR t
