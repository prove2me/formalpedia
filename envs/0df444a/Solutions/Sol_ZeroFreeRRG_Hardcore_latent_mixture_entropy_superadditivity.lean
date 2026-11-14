-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.latent_mixture_entropy_superadditivity
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:49:27.381562+00:00
-- url     : https://prove2.me/submissions/f292c0e8-451a-4e23-850e-3b4c10cb811d

import Theorems.Thm_ZeroFreeRRG_Hardcore_latent_mixture_density_support
import Theorems.Thm_ZeroFreeRRG_Hardcore_integrated_relative_entropy_nonnegative
import Theorems.Thm_ZeroFreeRRG_Hardcore_conditional_entropy_log_identity
import Mathlib
set_option autoImplicit false
open scoped BigOperators
open MeasureTheory ZeroFreeRRG.Hardcore

theorem solution {ι X : Type} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (A : ι → ℝ) (w : ι → X → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hS : 0 < ∑ i, A i)
    (hw : ∀ i x, 0 ≤ w i x) (hint : ∀ i, Integrable (w i) μ)
    (hmean : ∀ i, (∫ x, w i x ∂μ) = 1)
    (hTlog : Integrable (fun p : X × X =>
      (∑ i, A i*w i p.1*w i p.2)*Real.log (∑ i, A i*w i p.1*w i p.2)) (μ.prod μ))
    (hcrossL : Integrable (fun p : X × X =>
      (∑ i, A i*w i p.1*w i p.2)*Real.log (∑ i, A i*w i p.1)) (μ.prod μ))
    (hcrossR : Integrable (fun p : X × X =>
      (∑ i, A i*w i p.1*w i p.2)*Real.log (∑ i, A i*w i p.2)) (μ.prod μ)) :
    2*(∫ x, (∑ i, A i*w i x)*Real.log (∑ i, A i*w i x) ∂μ) ≤
      (∫ p : X × X, (∑ i, A i*w i p.1*w i p.2)*Real.log (∑ i, A i*w i p.1*w i p.2) ∂(μ.prod μ)) +
      (∑ i, A i)*Real.log (∑ i, A i) := by
  classical
  let S := ∑ i, A i
  let L : X → ℝ := fun x => ∑ i, A i*w i x
  let T : X × X → ℝ := fun p => ∑ i, A i*w i p.1*w i p.2
  let Q : X × X → ℝ := fun p => L p.1*L p.2/S
  have hS' : 0 < S := hS
  have hL : Integrable L μ := by
    dsimp [L]
    apply integrable_finsetSum
    intro i hi
    exact (hint i).const_mul (A i)
  have hLmean : (∫ x, L x ∂μ) = S := by
    dsimp [L,S]
    rw [integral_finsetSum _ (fun i hi => (hint i).const_mul (A i))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul, hmean]
    ring
  have hT : Integrable T (μ.prod μ) := by
    dsimp [T]
    apply integrable_finsetSum
    intro i hi
    change Integrable (fun p : X × X => A i*w i p.1*w i p.2) (μ.prod μ)
    convert ((hint i).mul_prod (hint i)).const_mul (A i) using 1
    funext p
    ring
  have hQ : Integrable Q (μ.prod μ) := (hL.mul_prod hL).div_const S
  have hTmean : (∫ p, T p ∂(μ.prod μ)) = S := by
    dsimp [T,S]
    have hi (i : ι) : Integrable (fun p : X × X => A i*w i p.1*w i p.2) (μ.prod μ) := by
      convert ((hint i).mul_prod (hint i)).const_mul (A i) using 1
      funext p
      ring
    rw [integral_finsetSum _ (fun i hi' => hi i)]
    apply Finset.sum_congr rfl
    intro i hi'
    have heq : (fun p : X × X => A i*w i p.1*w i p.2) =
        fun p => A i*(w i p.1*w i p.2) := by funext p; ring
    rw [heq, integral_const_mul, integral_prod_mul, hmean]
    ring
  have hQmean : (∫ p, Q p ∂(μ.prod μ)) = S := by
    dsimp [Q]
    rw [integral_div, integral_prod_mul, hLmean]
    field_simp
  have hsupport (p : X × X) : 0 ≤ T p ∧ 0 ≤ Q p ∧ (Q p=0 → T p=0) := by
    have hh := latent_mixture_density_support A (fun i => w i p.1) (fun i => w i p.2)
      hA (fun i => hw i p.1) (fun i => hw i p.2)
    exact hh
  have hlog (p : X × X) : T p*Real.log (Q p) =
      T p*Real.log (L p.1)+T p*Real.log (L p.2)-T p*Real.log S := by
    have hS0 : S=0 → T p=0 := by intro hz; exact False.elim (ne_of_gt hS' hz)
    have hL0 : L p.1=0 → T p=0 := by intro hz; apply (hsupport p).2.2; simp [Q,hz]
    have hR0 : L p.2=0 → T p=0 := by intro hz; apply (hsupport p).2.2; simp [Q,hz]
    exact conditional_entropy_log_identity S (L p.1) (L p.2) (T p) hS0 hL0 hR0
  have hlogint : Integrable (fun p => T p * Real.log (Q p)) (μ.prod μ) := by
    apply (hcrossL.add hcrossR |>.sub (hT.mul_const (Real.log S))).congr
    filter_upwards with p
    exact (hlog p).symm
  have hG := integrated_relative_entropy_nonnegative (μ.prod μ) T Q
    (Filter.Eventually.of_forall hsupport) hT hQ hTlog hlogint (hTmean.trans hQmean.symm)
  have hleft : (∫ p, T p * Real.log (L p.1) ∂(μ.prod μ)) =
      ∫ x, L x * Real.log (L x) ∂μ := by
    rw [integral_prod _ hcrossL]
    apply integral_congr_ae
    filter_upwards with x
    have hh : (fun y => T (x,y) * Real.log (L x)) =
        fun y => (∑ i, (A i*w i x)*w i y) * Real.log (L x) := rfl
    rw [hh, integral_mul_const, integral_finsetSum _ (fun i hi => (hint i).const_mul (A i*w i x))]
    congr 1
    dsimp [L]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul,hmean]
    ring
  have hright : (∫ p, T p * Real.log (L p.2) ∂(μ.prod μ)) =
      ∫ x, L x * Real.log (L x) ∂μ := by
    rw [integral_prod_symm _ hcrossR]
    apply integral_congr_ae
    filter_upwards with y
    have hh : (fun x => T (x,y) * Real.log (L y)) =
        fun x => (∑ i, (A i*w i y)*w i x) * Real.log (L y) := by
      funext x
      congr 1
      dsimp [T]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hh, integral_mul_const, integral_finsetSum _ (fun i hi => (hint i).const_mul (A i*w i y))]
    congr 1
    dsimp [L]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul,hmean]
    ring
  have hlogeq : (∫ p, T p * Real.log (Q p) ∂(μ.prod μ)) =
      2*(∫ x, L x * Real.log (L x) ∂μ)-S*Real.log S := by
    have hh : (fun p => T p * Real.log (Q p)) =
        fun p => T p*Real.log (L p.1)+T p*Real.log (L p.2)-T p*Real.log S := funext hlog
    rw [hh]
    have ha := integral_sub (hcrossL.add hcrossR) (hT.mul_const (Real.log S))
    have hb := integral_add hcrossL hcrossR
    simp only [Pi.add_apply, Pi.sub_apply] at ha hb
    rw [ha,hb,hleft,hright,integral_mul_const,hTmean]
    ring
  rw [hlogeq] at hG
  change _ ≤ (∫ p, T p * Real.log (T p) ∂(μ.prod μ)) + S*Real.log S
  linarith
