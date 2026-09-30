-- Prove2me | solution 1 for WeierstrassEllipticZeta.cleared_sigma_polynomial_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T01:09:07.71452+00:00
-- url     : https://prove2.me/submissions/49701567-d3d7-4776-9a5e-293b09afbc70

import Definitions.Def_WeierstrassEllipticZeta_PolynomialInterpolation
import Theorems.Thm_WeierstrassEllipticZeta_cleared_addition_entire_growth_weighted
import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_formula
import Theorems.Thm_WeierstrassEllipticZeta_wp_addition_formula
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

private lemma p2mL6_monomial_height (L : PeriodPair) (v : ℂ) (l a b c : ℕ)
    (habc : a+b+c ≤ 5*l) :
    1 + ‖weierstrassZeta L v ^ a * L.weierstrassP v ^ b *
      L.derivWeierstrassP v ^ c‖ ≤ ellipticInterpolationHeight L v l := by
  classical
  let i : Fin (5*l+1) × Fin (5*l+1) × Fin (5*l+1) :=
    (⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩)
  have hi : i ∈ Finset.univ.filter (fun j : Fin (5*l+1) × Fin (5*l+1) × Fin (5*l+1) =>
      j.1.val+j.2.1.val+j.2.2.val ≤ 5*l) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, habc⟩
  have hh := Finset.le_sup (f := fun j : Fin (5*l+1) × Fin (5*l+1) × Fin (5*l+1) =>
      (1 : ℝ≥0) + ‖weierstrassZeta L v ^ j.1.val * L.weierstrassP v ^ j.2.1.val *
        L.derivWeierstrassP v ^ j.2.2.val‖₊) hi
  exact_mod_cast hh

private lemma p2mL6_fixed_value_bound (L : PeriodPair) (v : ℂ) (l : ℕ) :
    1 ≤ ellipticInterpolationHeight L v l ∧
    (1 + ‖weierstrassZeta L v‖ + ‖L.weierstrassP v‖ + ‖L.derivWeierstrassP v‖)^(5*l) ≤
      (4:ℝ)^(5*l) * ellipticInterpolationHeight L v l := by
  have h0 := p2mL6_monomial_height L v l 0 0 0 (by omega)
  have ha := p2mL6_monomial_height L v l (5*l) 0 0 (by omega)
  have hb := p2mL6_monomial_height L v l 0 (5*l) 0 (by omega)
  have hc := p2mL6_monomial_height L v l 0 0 (5*l) (by omega)
  simp only [pow_zero, one_mul, mul_one, norm_one, norm_pow] at h0 ha hb hc
  let V := max 1 (max ‖weierstrassZeta L v‖ (max ‖L.weierstrassP v‖ ‖L.derivWeierstrassP v‖))
  have hV : 1 ≤ V := le_max_left _ _
  have hVa : ‖weierstrassZeta L v‖ ≤ V :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hVb : ‖L.weierstrassP v‖ ≤ V :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hVc : ‖L.derivWeierstrassP v‖ ≤ V :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hVp : V^(5*l) ≤ ellipticInterpolationHeight L v l := by
    dsimp only [V]
    rcases le_total 1 (max ‖weierstrassZeta L v‖
        (max ‖L.weierstrassP v‖ ‖L.derivWeierstrassP v‖)) with h1 | h1
    · rw [max_eq_right h1]
      rcases le_total ‖weierstrassZeta L v‖
          (max ‖L.weierstrassP v‖ ‖L.derivWeierstrassP v‖) with h2 | h2
      · rw [max_eq_right h2]
        rcases le_total ‖L.weierstrassP v‖ ‖L.derivWeierstrassP v‖ with h3 | h3
        · rw [max_eq_right h3]; linarith
        · rw [max_eq_left h3]; linarith
      · rw [max_eq_left h2]; linarith
    · rw [max_eq_left h1, one_pow]; linarith
  refine ⟨by linarith, ?_⟩
  calc
    _ ≤ (4*V)^(5*l) := pow_le_pow_left₀ (by positivity) (by linarith) _
    _ = (4:ℝ)^(5*l) * V^(5*l) := mul_pow _ _ _
    _ ≤ (4:ℝ)^(5*l) * ellipticInterpolationHeight L v l :=
      mul_le_mul_of_nonneg_left hVp (by positivity)

private lemma p2mL6_cleared_growth_constant (A R : ℝ) (hA : 0 < A)
    (hR : 1 ≤ R^2) (l : ℕ) :
    (36:ℝ)^(3*l) * (4:ℝ)^(5*l) * Real.exp (A*(1+R^2))^(15*l) ≤
      Real.exp (30*A+128) ^ (R^2*l) := by
  have h36 : (36:ℝ) ≤ Real.exp 36 := by linarith [Real.add_one_le_exp 36]
  have h4 : (4:ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp 4]
  calc
    _ ≤ (Real.exp 36)^(3*l) * (Real.exp 4)^(5*l) *
        Real.exp (A*(1+R^2))^(15*l) := by gcongr
    _ = Real.exp (128*l + 15*A*l*(1+R^2)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
        ← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      ring
    _ ≤ Real.exp ((30*A+128)*(R^2*l)) := by
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 128*(l:ℝ))
      have h2 := mul_le_mul_of_nonneg_left (by linarith : 1+R^2 ≤ 2*R^2)
        (by positivity : 0 ≤ 15*A*l)
      nlinarith
    _ = _ := Real.exp_mul _ _


theorem solution
    (L : PeriodPair) (σ : ℂ → ℂ) (S : Fin 3 → ℂ → ℂ)
    (hσ : AnalyticOnNhd ℂ σ univ) (hS : ∀ j, AnalyticOnNhd ℂ (S j) univ)
    (hrel : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 3,
      S j z = σ z ^ (j.val + 1) * ellipticPoleCoordinates L z j)
    (A : ℝ) (hA : 0 < A)
    (hgrowth : ∀ z : ℂ, ‖σ z‖ ≤ Real.exp (A * (1 + ‖z‖^2)) ∧
      ∀ j, ‖S j z‖ ≤ Real.exp (A * (1 + ‖z‖^2))) :
    ClearedSigmaPolynomialInterpolation L σ (Real.exp (30*A+128)) 1 := by
  intro d l hd hl p M hM hp v hv
  obtain ⟨G, hG, hGeq, hGb⟩ := cleared_addition_entire_growth_weighted L
    (zeta_addition_formula L) (wp_addition_formula L) σ S hσ hS hrel v hv p
    (fun i => i.1.val) (fun i => i.2.1.val) (fun i => i.2.2.val) d l
    (by intro i; exact Nat.le_of_lt_succ i.1.isLt)
    (by intro i; exact Nat.le_of_lt_succ i.2.1.isLt)
    (by intro i; exact Nat.le_of_lt_succ i.2.2.isLt)
  refine ⟨G, hG, ?_, ?_⟩
  · intro z hz hzv
    rw [hGeq z hz hzv]
    simp only [ellipticRectangularPolynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [clearedAdditionMonomial]
    ring
  · intro r R hr hrR hR₀ hvR u hu N s m hs hm hN t
    have hR : 0 < R := by linarith
    have hR2 : 1 ≤ R^2 := by nlinarith
    have hB : 1 ≤ Real.exp (A*(1+R^2)) := by
      apply Real.one_le_exp_iff.mpr
      positivity
    have hHt := p2mL6_fixed_value_bound L v l
    have hH0 : 0 ≤ ellipticInterpolationHeight L v l := by linarith [hHt.1]
    let C : ℝ := (d+1 : ℝ)*(l+1 : ℝ)^2*(5*l+1 : ℝ)^6*M*(2*R)^d *
      ellipticInterpolationHeight L v l * Real.exp (30*A+128) ^ (R^2*l)
    have hcircle (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) R) : ‖G z‖ ≤ C := by
      have hzR : ‖z‖ ≤ R := by simpa [mem_sphere_iff_norm] using le_of_eq hz
      have hb := hGb R (Real.exp (A*(1+R^2))) hB
        (p2mL6_growth_on_ball σ S A hA.le hgrowth R) z hzR
      let Q : ℝ := (d+1 : ℝ)*(l+1 : ℝ)^2*M*(2*R)^d
      have hQ : 0 ≤ Q := by dsimp [Q]; positivity
      have hb1 : ‖G z‖ ≤ Q * (36:ℝ)^(3*l) *
          (1+‖weierstrassZeta L v‖+‖L.weierstrassP v‖+‖L.derivWeierstrassP v‖)^(5*l) *
          Real.exp (A*(1+R^2))^(15*l) := by
        apply hb.trans
        dsimp [Q]
        gcongr
        · exact p2mL6_coefficient_sum d l p M hp
        · exact max_le (by linarith) (by linarith)
      have hb2 : ‖G z‖ ≤ Q * ellipticInterpolationHeight L v l *
          ((36:ℝ)^(3*l) * (4:ℝ)^(5*l) * Real.exp (A*(1+R^2))^(15*l)) := by
        apply hb1.trans
        calc
          _ ≤ Q*(36:ℝ)^(3*l) * ((4:ℝ)^(5*l)*ellipticInterpolationHeight L v l) *
              Real.exp (A*(1+R^2))^(15*l) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hHt.2 (by positivity)) (by positivity)
          _ = _ := by ring
      have hb3 := hb2.trans (mul_le_mul_of_nonneg_left
        (p2mL6_cleared_growth_constant A R hA hR2 l) (mul_nonneg hQ hH0))
      apply hb3.trans
      have hbase : (1:ℝ) ≤ 5*(l:ℝ)+1 := by
        have hl0 : (0:ℝ) ≤ l := Nat.cast_nonneg l
        linarith
      have hcomb : 1 ≤ (5*(l:ℝ)+1)^6 := one_le_pow₀ hbase
      calc
        _ ≤ (Q*ellipticInterpolationHeight L v l * Real.exp (30*A+128)^(R^2*l)) *
            (5*(l:ℝ)+1)^6 := le_mul_of_one_le_right (by positivity) hcomb
        _ = C := by dsimp [Q, C]; ring
    have hb := p2mL6_zero_threshold G hG s m r R C (by linarith) hrR
      (by dsimp [C]; positivity) hs hm hcircle N hN u hu t
    convert hb using 1 <;> dsimp [C] <;> push_cast <;> ring
