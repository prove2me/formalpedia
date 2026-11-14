-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.bounded_latent_mixture_entropy
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:02:48.28893+00:00
-- url     : https://prove2.me/submissions/c04951a9-2bad-404b-b1ef-10496dd169b8

import Theorems.Thm_ZeroFreeRRG_Hardcore_latent_mixture_entropy_superadditivity
import Mathlib
set_option autoImplicit false
open scoped BigOperators
open MeasureTheory ZeroFreeRRG.Hardcore

theorem solution {ι X : Type} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (A : ι → ℝ) (w : ι → X → ℝ) (C : ℝ)
    (hA : ∀ i, 0 ≤ A i) (hS : 0 < ∑ i, A i) (hC : 0 ≤ C)
    (hw : ∀ i x, 0 ≤ w i x ∧ w i x ≤ C) (hwm : ∀ i, Measurable (w i))
    (hmean : ∀ i, (∫ x, w i x ∂μ) = 1) :
    2*(∫ x, (∑ i, A i*w i x)*Real.log (∑ i, A i*w i x) ∂μ) ≤
      (∫ p : X × X, (∑ i, A i*w i p.1*w i p.2)*Real.log (∑ i, A i*w i p.1*w i p.2) ∂(μ.prod μ)) +
      (∑ i, A i)*Real.log (∑ i, A i) := by
  classical
  let S := ∑ i, A i
  let L : X → ℝ := fun x => ∑ i, A i*w i x
  let T : X × X → ℝ := fun p => ∑ i, A i*w i p.1*w i p.2
  have hS' : 0 < S := hS
  have hL0 (x : X) : 0 ≤ L x := Finset.sum_nonneg (fun i _ => mul_nonneg (hA i) (hw i x).1)
  have hT0 (p : X × X) : 0 ≤ T p := Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (hA i) (hw i p.1).1) (hw i p.2).1)
  have hLbound (x : X) : L x ≤ C*S := by
    dsimp [L,S]
    calc
      _ ≤ ∑ i, C*A i := Finset.sum_le_sum (fun i _ => by nlinarith [mul_nonneg (hA i) (sub_nonneg.mpr (hw i x).2)])
      _ = _ := by rw [Finset.mul_sum]
  have hTbound (p : X × X) : T p ≤ C*L p.1 := by
    dsimp [T,L]
    calc
      _ ≤ ∑ i, C*(A i*w i p.1) := Finset.sum_le_sum (fun i _ => by nlinarith [mul_nonneg (mul_nonneg (hA i) (hw i p.1).1) (sub_nonneg.mpr (hw i p.2).2)])
      _ = _ := by rw [Finset.mul_sum]
  have hTboundR (p : X × X) : T p ≤ C*L p.2 := by
    dsimp [T,L]
    calc
      _ ≤ ∑ i, C*(A i*w i p.2) := Finset.sum_le_sum (fun i _ => by nlinarith [mul_nonneg (mul_nonneg (hA i) (hw i p.2).1) (sub_nonneg.mpr (hw i p.1).2)])
      _ = _ := by rw [Finset.mul_sum]
  have hTupper (p : X × X) : T p ≤ C^2*S := by
    have hh := mul_le_mul_of_nonneg_left (hLbound p.1) hC
    nlinarith [hTbound p]
  have hmL : Measurable L := by
    dsimp [L]
    fun_prop
  have hmT : Measurable T := by
    dsimp [T]
    fun_prop
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) (C*S))).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  obtain ⟨D,hD⟩ := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) (C^2*S))).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  have hTlog : Integrable (fun p => T p*Real.log (T p)) (μ.prod μ) := by
    apply Integrable.of_bound (hmT.mul hmT.log).aestronglyMeasurable D
    filter_upwards with p
    exact hD _ ⟨hT0 p,hTupper p⟩
  have hcrossL : Integrable (fun p => T p*Real.log (L p.1)) (μ.prod μ) := by
    apply Integrable.of_bound (hmT.mul (hmL.comp measurable_fst).log).aestronglyMeasurable (C*B)
    filter_upwards with p
    change ‖T p*Real.log (L p.1)‖ ≤ C*B
    have hh := hB (L p.1) ⟨hL0 p.1,hLbound p.1⟩
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hT0 p), abs_of_nonneg (hL0 p.1)] at *
    have hlog := abs_nonneg (Real.log (L p.1))
    have hh' := mul_le_mul_of_nonneg_right (hTbound p) hlog
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hh)]
  have hcrossR : Integrable (fun p => T p*Real.log (L p.2)) (μ.prod μ) := by
    apply Integrable.of_bound (hmT.mul (hmL.comp measurable_snd).log).aestronglyMeasurable (C*B)
    filter_upwards with p
    change ‖T p*Real.log (L p.2)‖ ≤ C*B
    have hh := hB (L p.2) ⟨hL0 p.2,hLbound p.2⟩
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hT0 p), abs_of_nonneg (hL0 p.2)] at *
    have hlog := abs_nonneg (Real.log (L p.2))
    have hh' := mul_le_mul_of_nonneg_right (hTboundR p) hlog
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hh)]
  have hint (i : ι) : Integrable (w i) μ := by
    apply Integrable.of_bound (hwm i).aestronglyMeasurable C
    filter_upwards with x
    simpa [Real.norm_eq_abs, abs_of_nonneg (hw i x).1] using (hw i x).2
  exact latent_mixture_entropy_superadditivity μ A w hA hS (fun i x => (hw i x).1)
    hint hmean hTlog hcrossL hcrossR
