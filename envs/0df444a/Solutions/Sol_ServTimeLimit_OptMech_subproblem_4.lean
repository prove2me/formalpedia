-- Prove2me | solution 1 for ServTimeLimit.OptMech.subproblem_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T22:45:56.967248+00:00
-- url     : https://prove2.me/submissions/872fc2b1-4e98-42c7-84e9-287db6e510cd

import Mathlib
import Definitions.Def_ServTimeLimit_OptMech_Model

open MeasureTheory

namespace Aux_ServTimeLimit_OptMech_subproblem_4

lemma key {μ : Measure ℝ} [IsFiniteMeasure μ] (t m : ℝ → ℝ) (C B : ℝ)
    (htm : Measurable t) (hmm : Measurable m)
    (hb : ∀ᵐ θ ∂μ, |t θ| ≤ B ∧ |m θ| ≤ B)
    (hint : ∫ θ, t θ ∂μ = ∫ θ, m θ ∂μ)
    (hcross : ∀ᵐ θ ∂μ, 0 ≤ (m θ - C) * (t θ - m θ)) :
    (∫ θ, m θ ^ 2 ∂μ) ≤ ∫ θ, t θ ^ 2 ∂μ ∧
      ((∫ θ, m θ ^ 2 ∂μ) = ∫ θ, t θ ^ 2 ∂μ → t =ᵐ[μ] m) := by
  have iB : ∀ (f : ℝ → ℝ) (K : ℝ), Measurable f → (∀ᵐ θ ∂μ, |f θ| ≤ K) → Integrable f μ :=
    fun f K hf hK => Integrable.of_bound hf.aestronglyMeasurable K
      (hK.mono (fun θ h => by rw [Real.norm_eq_abs]; exact h))
  have ht : Integrable t μ := iB t B htm (hb.mono (fun θ h => h.1))
  have hm : Integrable m μ := iB m B hmm (hb.mono (fun θ h => h.2))
  have hd2 : Integrable (fun θ => (t θ - m θ) ^ 2) μ :=
    iB _ ((2 * B) ^ 2) ((htm.sub hmm).pow_const 2) (hb.mono (fun θ h => by
      rw [abs_of_nonneg (sq_nonneg _)]
      have h1 : |t θ - m θ| ≤ 2 * B := by
        calc |t θ - m θ| ≤ |t θ| + |m θ| := abs_sub _ _
          _ ≤ 2 * B := by linarith [h.1, h.2]
      calc (t θ - m θ) ^ 2 = |t θ - m θ| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * B) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2))
  have hm2 : Integrable (fun θ => m θ ^ 2) μ :=
    iB _ (B ^ 2) (hmm.pow_const 2) (hb.mono (fun θ h => by
      rw [abs_of_nonneg (sq_nonneg _)]
      calc m θ ^ 2 = |m θ| ^ 2 := (sq_abs _).symm
        _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h.2 2))
  have hcr : Integrable (fun θ => (m θ - C) * (t θ - m θ)) μ :=
    iB _ ((B + |C|) * (2 * B)) ((hmm.sub measurable_const).mul (htm.sub hmm))
      (hb.mono (fun θ h => by
        rw [abs_mul]
        have h1 : |m θ - C| ≤ B + |C| := (abs_sub _ _).trans (by linarith [h.2])
        have h2 : |t θ - m θ| ≤ 2 * B := (abs_sub _ _).trans (by linarith [h.1, h.2])
        exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)))
  have hid : ∀ θ, t θ ^ 2 = m θ ^ 2 + (t θ - m θ) ^ 2 + 2 * ((m θ - C) * (t θ - m θ)) +
      2 * C * (t θ - m θ) := fun θ => by ring
  have hI : ∫ θ, t θ ^ 2 ∂μ = ∫ θ, m θ ^ 2 ∂μ + ∫ θ, (t θ - m θ) ^ 2 ∂μ +
      2 * ∫ θ, (m θ - C) * (t θ - m θ) ∂μ + 2 * C * (∫ θ, t θ ∂μ - ∫ θ, m θ ∂μ) := by
    simp_rw [hid]
    have i1 : Integrable (fun θ => m θ ^ 2 + (t θ - m θ) ^ 2) μ := hm2.add hd2
    have i2 : Integrable (fun θ => 2 * ((m θ - C) * (t θ - m θ))) μ := hcr.const_mul 2
    have i3 : Integrable (fun θ => m θ ^ 2 + (t θ - m θ) ^ 2 + 2 * ((m θ - C) * (t θ - m θ))) μ :=
      i1.add i2
    have i4 : Integrable (fun θ => 2 * C * (t θ - m θ)) μ := (ht.sub hm).const_mul (2 * C)
    have i5 : Integrable (fun θ => t θ - m θ) μ := ht.sub hm
    rw [integral_add i3 i4, integral_add i1 i2, integral_add hm2 hd2,
      integral_const_mul, integral_const_mul, integral_sub ht hm]
  rw [hint, sub_self, mul_zero, add_zero] at hI
  have h1 : 0 ≤ ∫ θ, (t θ - m θ) ^ 2 ∂μ := integral_nonneg (fun θ => sq_nonneg _)
  have h2 : 0 ≤ ∫ θ, (m θ - C) * (t θ - m θ) ∂μ := integral_nonneg_of_ae hcross
  refine ⟨by linarith, fun heq => ?_⟩
  have h3 : ∫ θ, (t θ - m θ) ^ 2 ∂μ = 0 := by linarith
  have h4 := (integral_eq_zero_iff_of_nonneg (fun θ => sq_nonneg (t θ - m θ)) hd2).1 h3
  filter_upwards [h4] with θ hθ
  have : (t θ - m θ) ^ 2 = 0 := hθ
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  linarith

end Aux_ServTimeLimit_OptMech_subproblem_4

open Aux_ServTimeLimit_OptMech_subproblem_4 in
open ServTimeLimit.OptMech in
theorem solution (a b k : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    (0 ≤ k → k ≤ a * (b - a) →
      (∀ θ ∈ Set.Icc a b, 0 ≤ k / (b - a) ∧ k / (b - a) ≤ θ) ∧
      (∫ _θ in Set.Icc a b, k / (b - a)) = k ∧
      ∀ t : ℝ → ℝ, Measurable t → (∀ θ ∈ Set.Icc a b, 0 ≤ t θ ∧ t θ ≤ θ) →
        (∫ θ in Set.Icc a b, t θ) = k →
        (∫ _θ in Set.Icc a b, (k / (b - a)) ^ 2) ≤ ∫ θ in Set.Icc a b, t θ ^ 2 ∧
        ((∫ _θ in Set.Icc a b, (k / (b - a)) ^ 2) = ∫ θ in Set.Icc a b, t θ ^ 2 →
          t =ᵐ[volume.restrict (Set.Icc a b)] fun _ => k / (b - a))) ∧
    (a * (b - a) ≤ k → k ≤ (b ^ 2 - a ^ 2) / 2 →
      ∀ T : ℝ, T = b - Real.sqrt (b ^ 2 - a ^ 2 - 2 * k) →
      a ≤ T ∧ T ≤ b ∧
      (∫ θ in Set.Icc a b, min θ T) = k ∧
      ∀ t : ℝ → ℝ, Measurable t → (∀ θ ∈ Set.Icc a b, 0 ≤ t θ ∧ t θ ≤ θ) →
        (∫ θ in Set.Icc a b, t θ) = k →
        (∫ θ in Set.Icc a b, (min θ T) ^ 2) ≤ ∫ θ in Set.Icc a b, t θ ^ 2 ∧
        ((∫ θ in Set.Icc a b, (min θ T) ^ 2) = ∫ θ in Set.Icc a b, t θ ^ 2 →
          t =ᵐ[volume.restrict (Set.Icc a b)] fun θ => min θ T)) := by
  have hL : 0 < b - a := by linarith
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hvol : volume.real (Set.Icc a b) = b - a := by
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal hL.le]
  have haeI : ∀ᵐ θ ∂(volume.restrict (Set.Icc a b)), θ ∈ Set.Icc a b :=
    ae_restrict_mem measurableSet_Icc
  constructor
  · intro hk0 hk1
    have hc0 : 0 ≤ k / (b - a) := div_nonneg hk0 hL.le
    have hc1 : k / (b - a) ≤ a := by rw [div_le_iff₀ hL]; linarith
    have hconst : (∫ _θ in Set.Icc a b, k / (b - a)) = k := by
      rw [setIntegral_const, hvol, smul_eq_mul]
      field_simp
    refine ⟨fun θ hθ => ⟨hc0, hc1.trans hθ.1⟩, hconst, ?_⟩
    intro t htm ht htk
    have hb : ∀ᵐ θ ∂(volume.restrict (Set.Icc a b)),
        |t θ| ≤ b ∧ |(fun _ : ℝ => k / (b - a)) θ| ≤ b := by
      filter_upwards [haeI] with θ hθ
      have h := ht θ hθ
      refine ⟨?_, ?_⟩
      · rw [abs_of_nonneg h.1]; linarith [hθ.2]
      · rw [abs_of_nonneg hc0]; linarith
    exact key t (fun _ => k / (b - a)) (k / (b - a)) b htm measurable_const hb
      (by rw [htk, hconst]) (Filter.Eventually.of_forall (fun θ => by simp))
  · intro hk1 hk2 T hT
    have hrad : 0 ≤ b ^ 2 - a ^ 2 - 2 * k := by linarith
    set s := Real.sqrt (b ^ 2 - a ^ 2 - 2 * k) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = b ^ 2 - a ^ 2 - 2 * k := Real.sq_sqrt hrad
    have hsle : s ≤ b - a := by
      have : b ^ 2 - a ^ 2 - 2 * k ≤ (b - a) ^ 2 := by nlinarith
      calc s ≤ Real.sqrt ((b - a) ^ 2) := Real.sqrt_le_sqrt this
        _ = b - a := Real.sqrt_sq hL.le
    have hTa : a ≤ T := by rw [hT]; linarith
    have hTb : T ≤ b := by rw [hT]; linarith
    have hcont : Continuous (fun θ : ℝ => min θ T) := continuous_id.min continuous_const
    have hmint : (∫ θ in Set.Icc a b, min θ T) = k := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le,
        ← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable a T)
          (hcont.intervalIntegrable T b)]
      have e1 : ∫ θ in a..T, min θ T = ∫ θ in a..T, θ := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        rw [Set.uIcc_of_le hTa] at hθ
        exact min_eq_left hθ.2
      have e2 : ∫ θ in T..b, min θ T = ∫ _θ in T..b, T := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        rw [Set.uIcc_of_le hTb] at hθ
        exact min_eq_right hθ.1
      rw [e1, e2, integral_id, intervalIntegral.integral_const, smul_eq_mul]
      have hT' : T = b - s := hT
      rw [hT']
      nlinarith [hs2]
    refine ⟨hTa, hTb, hmint, ?_⟩
    intro t htm ht htk
    have hb : ∀ᵐ θ ∂(volume.restrict (Set.Icc a b)), |t θ| ≤ b ∧ |min θ T| ≤ b := by
      filter_upwards [haeI] with θ hθ
      have h := ht θ hθ
      refine ⟨?_, ?_⟩
      · rw [abs_of_nonneg h.1]; linarith [hθ.2]
      · rw [abs_of_nonneg (le_min (ha.trans hθ.1) (ha.trans hTa))]
        exact (min_le_left _ _).trans hθ.2
    have hcross : ∀ᵐ θ ∂(volume.restrict (Set.Icc a b)),
        0 ≤ (min θ T - T) * (t θ - min θ T) := by
      filter_upwards [haeI] with θ hθ
      rcases le_total θ T with h | h
      · rw [min_eq_left h]
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [(ht θ hθ).2])
      · rw [min_eq_right h, sub_self, zero_mul]
    exact key t (fun θ => min θ T) T b htm hcont.measurable hb (by rw [htk, hmint]) hcross
