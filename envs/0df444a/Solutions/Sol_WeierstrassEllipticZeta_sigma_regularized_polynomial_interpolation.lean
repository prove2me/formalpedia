-- Prove2me | solution 1 for WeierstrassEllipticZeta.sigma_regularized_polynomial_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T01:09:06.743043+00:00
-- url     : https://prove2.me/submissions/43044da8-9f4d-4752-a915-e8ebfe51e338

import Definitions.Def_WeierstrassEllipticZeta_PolynomialInterpolation
import Theorems.Thm_TranscendenceTheory_exists_entire_monomial_regularization
import Theorems.Thm_TranscendenceTheory_finite_zeros_derivative_bound
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr

noncomputable section
open Finset Set WeierstrassEllipticZeta
open scoped NNReal

private lemma p2mL6_zero_threshold (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ) (s : Finset ℂ) (m : ℂ → ℕ)
    (r R C : ℝ) (hr : 0 < r) (hrR : r < R) (hC0 : 0 ≤ C)
    (hs : ∀ a ∈ s, ‖a‖ < r)
    (hm : ∀ a ∈ s, ∀ j < m a, iteratedDeriv j f a = 0)
    (hC : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ C)
    (N : ℕ) (hN : N ≤ ∑ a ∈ s, m a) (v : ℂ) (hv : ‖v‖ < r-2) (t : ℕ) :
    ‖iteratedDeriv t f v‖ ≤ t.factorial * (C * (2*r/R)^N) := by
  have hR : 0 < R := hr.trans hrR
  have hv1 : ‖v‖ + 1 ≤ r := by linarith
  by_cases hq : 2*r/R ≤ 1
  · have hb := (TranscendenceTheory.finite_zeros_derivative_bound f hf s m hm
      r R C hr hrR (fun a ha => (hs a ha).le) hC).2 v 1 (by norm_num) hv1 t
    simp only [one_pow, div_one] at hb
    apply hb.trans
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) hq hN) hC0)
      (Nat.cast_nonneg _)
  · have hb := (TranscendenceTheory.finite_zeros_derivative_bound f hf ∅
      (fun _ => 0) (by simp) r R C hr hrR (by simp) hC).2
      v 1 (by norm_num) hv1 t
    simp only [Finset.sum_empty, pow_zero, mul_one, one_pow, div_one] at hb
    apply hb.trans
    have hone : 1 ≤ (2*r/R)^N := one_le_pow₀ (by linarith)
    calc
      (t.factorial : ℝ) * C = t.factorial * (C * 1) := by ring
      _ ≤ t.factorial * (C * (2*r/R)^N) := by gcongr

private lemma p2mL6_coefficient_sum (d l : ℕ)
    (p : EllipticPolynomialIndex d l → ℂ) (M : ℝ) (h : ∀ i, ‖p i‖ ≤ M) :
    (∑ i, ‖p i‖) ≤ (d+1 : ℝ) * (l+1 : ℝ)^2 * M := by
  calc
    (∑ i, ‖p i‖) ≤ ∑ _i : EllipticPolynomialIndex d l, M :=
      Finset.sum_le_sum (fun i _ => h i)
    _ = (d+1 : ℝ) * (l+1 : ℝ)^2 * M := by
      simp only [Finset.sum_const, Finset.card_univ, EllipticPolynomialIndex,
        Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one]
      ring

private lemma p2mL6_growth_on_ball (σ : ℂ → ℂ) (S : Fin 3 → ℂ → ℂ)
    (A : ℝ) (hA : 0 ≤ A)
    (hgrowth : ∀ z : ℂ, ‖σ z‖ ≤ Real.exp (A*(1+‖z‖^2)) ∧
      ∀ j, ‖S j z‖ ≤ Real.exp (A*(1+‖z‖^2)))
    (R : ℝ) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖σ z‖ ≤ Real.exp (A*(1+R^2)) ∧ ∀ j, ‖S j z‖ ≤ Real.exp (A*(1+R^2)) := by
  have hb : Real.exp (A*(1+‖z‖^2)) ≤ Real.exp (A*(1+R^2)) := by
    apply Real.exp_le_exp.mpr
    gcongr
  exact ⟨(hgrowth z).1.trans hb, fun j => ((hgrowth z).2 j).trans hb⟩


theorem solution
    (L : PeriodPair) (σ : ℂ → ℂ) (S : Fin 3 → ℂ → ℂ)
    (hσ : AnalyticOnNhd ℂ σ univ) (hS : ∀ j, AnalyticOnNhd ℂ (S j) univ)
    (hrel : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 3,
      S j z = σ z ^ (j.val + 1) * ellipticPoleCoordinates L z j)
    (A : ℝ) (hA : 0 < A)
    (hgrowth : ∀ z : ℂ, ‖σ z‖ ≤ Real.exp (A * (1 + ‖z‖^2)) ∧
      ∀ j, ‖S j z‖ ≤ Real.exp (A * (1 + ‖z‖^2))) :
    SigmaPolynomialInterpolation L σ (Real.exp (15*A)) 1 := by
  intro d l hd hl p M hM hp u
  let e : EllipticPolynomialIndex d l → Fin 3 → ℕ :=
    fun i => ![i.2.2.val, i.2.1.val, 0]
  have he (i : EllipticPolynomialIndex d l) :
      ∑ j : Fin 3, (j.val+1) * e i j ≤ 3*l := by
    simp [e, Fin.sum_univ_succ]
    have h1 := i.2.1.isLt
    have h2 := i.2.2.isLt
    omega
  obtain ⟨H, hH, hHeq, hHb⟩ :=
    TranscendenceTheory.exists_entire_monomial_regularization
      (L.lattice : Set ℂ)ᶜ σ (fun j z => ellipticPoleCoordinates L z j) S hσ hS
      (fun j => j.val+1) (by intro j; omega) hrel 0 p
      (fun i => i.1.val) e d (3*l) (by intro i; exact Nat.le_of_lt_succ i.1.isLt) he
  refine ⟨fun z => H (z+u), ?_, ?_, ?_⟩
  · intro z _
    exact (hH (z+u) trivial).comp (f := fun w : ℂ => w+u)
      (analyticAt_id.add analyticAt_const)
  · intro z hz
    dsimp only
    rw [hHeq (z+u) hz]
    congr 1
    simp [ellipticRectangularPolynomial, e, Fin.prod_univ_succ,
      ellipticPoleCoordinates, mul_comm, mul_left_comm, mul_assoc]
  · intro r R hr hrR hR₀ hu v hv N s m hs hm hN t
    have hR : 0 < R := by linarith
    have hR2 : 1 ≤ R^2 := by nlinarith
    have hB : 1 ≤ Real.exp (A*(1+(2*R)^2)) := by
      apply Real.one_le_exp_iff.mpr
      positivity
    have hexp : Real.exp (A*(1+(2*R)^2))^(3*l) ≤
        Real.exp (15*A) ^ (R^2*l) := by
      rw [← Real.exp_nat_mul, ← Real.exp_mul]
      apply Real.exp_le_exp.mpr
      push_cast
      have hb : 1+(2*R)^2 ≤ 5*R^2 := by nlinarith
      calc
        (3*(l : ℝ)) * (A*(1+(2*R)^2)) = (3*l*A)*(1+(2*R)^2) := by ring
        _ ≤ (3*l*A)*(5*R^2) := mul_le_mul_of_nonneg_left hb (by positivity)
        _ = (15*A)*(R^2*l) := by ring
    let C : ℝ := (d+1 : ℝ)*(l+1 : ℝ)^2*M*(2*R)^d *
      Real.exp (15*A) ^ (R^2*l)
    have hcircle (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) R) :
        ‖H (z+u)‖ ≤ C := by
      have hzR : ‖z‖ = R := by simpa [mem_sphere_iff_norm] using hz
      have hzu : ‖z+u‖ ≤ 2*R := (norm_add_le z u).trans (by linarith)
      have hb := hHb (2*R) (Real.exp (A*(1+(2*R)^2))) hB
        (p2mL6_growth_on_ball σ S A hA.le hgrowth (2*R)) (z+u) hzu
      simp only [norm_zero, add_zero] at hb
      rw [max_eq_right (by linarith : (1:ℝ) ≤ 2*R)] at hb
      apply hb.trans
      dsimp only [C]
      exact mul_le_mul (mul_le_mul_of_nonneg_right
        (p2mL6_coefficient_sum d l p M hp) (by positivity)) hexp
        (by positivity) (by positivity)
    have hb := p2mL6_zero_threshold (fun z => H (z+u))
      (fun z _ => (hH (z+u) trivial).comp (f := fun w : ℂ => w+u)
        (analyticAt_id.add analyticAt_const))
      s m r R C (by linarith) hrR (by dsimp [C]; positivity) hs hm hcircle N hN v hv t
    convert hb using 1 <;> dsimp [C] <;> push_cast <;> ring
