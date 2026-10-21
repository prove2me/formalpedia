-- Prove2me | solution 1 for PriceQualityService.Uniform.root_quasiconvex
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:33:10.824087+00:00
-- url     : https://prove2.me/submissions/dfec3cc5-03aa-41b8-9ba1-de9092ba73f3

import Mathlib
import Definitions.Def_PriceQualityService_Uniform_Reduction

set_option autoImplicit false
open PriceQualityService.Uniform Finset

theorem y_convex' {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) :
    ConvexOn ℝ Set.univ (yTotal α a b c s) := by
  have hexp : ∀ i, ConvexOn ℝ Set.univ (fun t => Real.exp (exponent α a b c s t i)) := by
    intro i
    have hqc : ConvexOn ℝ Set.univ (fun t : ℝ => exponent α a b c s t i) := by
      refine ⟨convex_univ, ?_⟩
      intro x _ y _ p q hp hq hpq
      have hci : 0 < 4 * c i := by linarith [hc i]
      have hq1 : q = 1 - p := by linarith
      have key : 0 ≤ b i ^ 2 / (4 * c i) * (p * x ^ 2 + q * y ^ 2 - (p * x + q * y) ^ 2) := by
        apply mul_nonneg (div_nonneg (sq_nonneg _) hci.le)
        have : p * x ^ 2 + q * y ^ 2 - (p * x + q * y) ^ 2 = p * q * (x - y) ^ 2 := by
          rw [hq1]; ring
        rw [this]; positivity
      simp only [exponent, smul_eq_mul]
      have e1 : b i ^ 2 * (p * x + q * y) ^ 2 / (4 * c i) =
          b i ^ 2 / (4 * c i) * (p * x + q * y) ^ 2 := by ring
      have e2 : b i ^ 2 * x ^ 2 / (4 * c i) = b i ^ 2 / (4 * c i) * x ^ 2 := by ring
      have e3 : b i ^ 2 * y ^ 2 / (4 * c i) = b i ^ 2 / (4 * c i) * y ^ 2 := by ring
      rw [e1, e2, e3]
      have : α i ^ 2 / (4 * c i) = p * (α i ^ 2 / (4 * c i)) + q * (α i ^ 2 / (4 * c i)) := by
        rw [← add_mul, hpq, one_mul]
      nlinarith [key, this]
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ p q hp hq' hpq
    have h1 := hqc.2 (Set.mem_univ x) (Set.mem_univ y) hp hq' hpq
    have h2 := convexOn_exp.2 (Set.mem_univ (exponent α a b c s x i))
      (Set.mem_univ (exponent α a b c s y i)) hp hq' hpq
    simp only [smul_eq_mul] at h1 h2 ⊢
    exact (Real.exp_le_exp.mpr h1).trans h2
  have hsum : ∀ S : Finset (Fin N),
      ConvexOn ℝ Set.univ (fun t => ∑ i ∈ S, Real.exp (exponent α a b c s t i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using convexOn_const (0 : ℝ) convex_univ
    | insert i S hi ih =>
      simp_rw [Finset.sum_insert hi]
      exact (hexp i).add ih
  exact hsum Finset.univ

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

theorem eq25' {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) :
    (∀ r t : ℝ, r = ∑ i, gTerm α a b c s r t i ↔ r = yTotal α a b c s t / Real.exp (1 + r)) ∧
    ∀ R : ℝ → ℝ, (∀ t, R t = ∑ i, gTerm α a b c s (R t) t i) →
      ∀ t t' : ℝ, yTotal α a b c s t ≤ yTotal α a b c s t' → R t ≤ R t' := by
  refine ⟨fun r t => by rw [sum_gTerm'], ?_⟩
  intro R hR t t' hyt
  have h1 : R t = yTotal α a b c s t / Real.exp (1 + R t) := by
    rw [← sum_gTerm']; exact hR t
  have h2 : R t' = yTotal α a b c s t' / Real.exp (1 + R t') := by
    rw [← sum_gTerm']; exact hR t'
  by_contra hlt
  push Not at hlt
  have hexp : Real.exp (1 + R t') ≤ Real.exp (1 + R t) := Real.exp_le_exp.mpr (by linarith)
  have hp' : 0 < Real.exp (1 + R t') := Real.exp_pos _
  have hp : 0 < Real.exp (1 + R t) := Real.exp_pos _
  have : R t ≤ R t' := by
    rw [h1, h2]
    calc yTotal α a b c s t / Real.exp (1 + R t)
        ≤ yTotal α a b c s t' / Real.exp (1 + R t) := by
          exact div_le_div_of_nonneg_right hyt hp.le
      _ ≤ yTotal α a b c s t' / Real.exp (1 + R t') := by
          exact div_le_div_of_nonneg_left (yTotal_nonneg' α a b c s t') hp' hexp
  linarith

theorem solution {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (R : ℝ → ℝ)
    (hR : ∀ t, R t = ∑ i, gTerm α a b c s (R t) t i) :
    QuasiconvexOn ℝ Set.univ R := by
  have hyc := y_convex' α a b c s hc
  have hmono := (eq25' α a b c s hc).2 R hR
  intro r x hx y hy p q hp hq hpq
  refine ⟨Set.mem_univ _, ?_⟩
  have h1 := hyc.2 (Set.mem_univ x) (Set.mem_univ y) hp hq hpq
  simp only [smul_eq_mul] at h1 ⊢
  have hq1 : q = 1 - p := by linarith
  subst hq1
  rcases le_total (yTotal α a b c s x) (yTotal α a b c s y) with h | h
  · have h2 : yTotal α a b c s (p * x + (1 - p) * y) ≤ yTotal α a b c s y := by
      nlinarith [h, h1, mul_nonneg hp (sub_nonneg.2 h)]
    exact (hmono _ _ h2).trans hy.2
  · have h2 : yTotal α a b c s (p * x + (1 - p) * y) ≤ yTotal α a b c s x := by
      nlinarith [h, h1, mul_nonneg hq (sub_nonneg.2 h)]
    exact (hmono _ _ h2).trans hx.2
