-- Prove2me | solution 1 for SepMeasures.claim_3_4
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T02:59:05.299781+00:00
-- url     : https://prove2.me/submissions/1e943a0a-732d-4e32-8b26-3f86e0757754

import Mathlib

open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (U W : Ω → ℝ) (hU : Measurable U) (hW : Measurable W)
    (hU1 : ℙ {ω | U ω = 1} = 1 / 2) (hUm1 : ℙ {ω | U ω = -1} = 1 / 2)
    (hWb : ∀ᵐ ω ∂ℙ, W ω ∈ Set.Icc (-1 : ℝ) 1) :
    |∫ ω, W ω ∂ℙ| + |∫ ω, U ω * W ω ∂ℙ| ≤ 1 := by
  classical
  have key : ∀ a b : ℝ, |a| ≤ 1 / 2 → |b| ≤ 1 / 2 → |a + b| + |a - b| ≤ 1 := by
    intro a b ha hb
    have ha2 : a ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs a, abs_nonneg a]
    have hb2 : b ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs b, abs_nonneg b]
    have hX : 0 ≤ |a + b| := abs_nonneg _
    have hY : 0 ≤ |a - b| := abs_nonneg _
    have h1 : |a + b| ^ 2 = (a + b) ^ 2 := sq_abs _
    have h2 : |a - b| ^ 2 = (a - b) ^ 2 := sq_abs _
    have h3 : |a + b| * |a - b| = |a ^ 2 - b ^ 2| := by
      rw [← abs_mul]
      ring_nf
    have hsq : (|a + b| + |a - b|) ^ 2 ≤ 1 := by
      rcases le_total (a ^ 2) (b ^ 2) with hle | hle
      · have h4 : |a ^ 2 - b ^ 2| = -(a ^ 2 - b ^ 2) := abs_of_nonpos (by linarith)
        nlinarith [hb2]
      · have h4 : |a ^ 2 - b ^ 2| = a ^ 2 - b ^ 2 := abs_of_nonneg (by linarith)
        nlinarith [ha2]
    nlinarith [hsq, hX, hY, sq_nonneg (|a + b| + |a - b| - 1)]
  set A : Set Ω := {ω | U ω = 1} with hAdef
  set B : Set Ω := {ω | U ω = -1} with hBdef
  have hA : MeasurableSet A := by rw [hAdef]; exact hU (measurableSet_singleton 1)
  have hB : MeasurableSet B := by rw [hBdef]; exact hU (measurableSet_singleton (-1))
  have hU1' : ℙ A = 1 / 2 := by rw [hAdef]; exact hU1
  have hUm1' : ℙ B = 1 / 2 := by rw [hBdef]; exact hUm1
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro ω h1 h2
    rw [hAdef] at h1
    rw [hBdef] at h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    linarith
  have hcover : ℙ (A ∪ B) = 1 := by
    rw [measure_union hAB hB, hU1', hUm1']
    simpa using ENNReal.add_halves (1 : ENNReal)
  have hcompl : ℙ (A ∪ B)ᶜ = 0 := by
    rw [measure_compl (hA.union hB) (measure_ne_top _ _), hcover]
    simp
  have hae : ∀ᵐ ω ∂ℙ, ω ∈ A ∪ B := by
    rw [ae_iff]
    change ℙ (A ∪ B)ᶜ = 0
    exact hcompl
  have hWabs : ∀ᵐ ω ∂ℙ, |W ω| ≤ 1 := by
    filter_upwards [hWb] with ω hω
    exact abs_le.mpr hω
  have hWint : Integrable W ℙ := by
    refine Integrable.of_bound hW.aestronglyMeasurable 1 ?_
    filter_upwards [hWb] with ω hω
    simpa using abs_le.mpr hω
  have hUWabs : ∀ᵐ ω ∂ℙ, |U ω * W ω| ≤ 1 := by
    filter_upwards [hWb, hae] with ω hω hmem
    rcases hmem with h | h
    · rw [hAdef] at h
      simp only [Set.mem_ofPred_eq] at h
      rw [h, one_mul]
      exact abs_le.mpr hω
    · rw [hBdef] at h
      simp only [Set.mem_ofPred_eq] at h
      rw [h, neg_one_mul, abs_neg]
      exact abs_le.mpr hω
  have hUWint : Integrable (fun ω => U ω * W ω) ℙ := by
    refine Integrable.of_bound (hU.mul hW).aestronglyMeasurable 1 ?_
    simpa using hUWabs
  have hWsup : ∫ x in A ∪ B, W x ∂ℙ = ∫ x, W x ∂ℙ := by
    refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    filter_upwards [hae] with x hx hxnot
    exact absurd hx hxnot
  have hWsplit : ∫ x in A ∪ B, W x ∂ℙ = ∫ x in A, W x ∂ℙ + ∫ x in B, W x ∂ℙ :=
    setIntegral_union hAB hB hWint.integrableOn hWint.integrableOn
  have hWfinal : ∫ x, W x ∂ℙ = (∫ x in A, W x ∂ℙ) + ∫ x in B, W x ∂ℙ := by
    rw [← hWsup, hWsplit]
  have hUWsup : ∫ x in A ∪ B, U x * W x ∂ℙ = ∫ x, U x * W x ∂ℙ := by
    refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    filter_upwards [hae] with x hx hxnot
    exact absurd hx hxnot
  have hUWsplit : ∫ x in A ∪ B, U x * W x ∂ℙ
      = ∫ x in A, U x * W x ∂ℙ + ∫ x in B, U x * W x ∂ℙ :=
    setIntegral_union hAB hB hUWint.integrableOn hUWint.integrableOn
  have hAeq : ∫ x in A, U x * W x ∂ℙ = ∫ x in A, W x ∂ℙ := by
    refine setIntegral_congr_fun hA ?_
    intro x hx
    rw [hAdef] at hx
    simp only [Set.mem_ofPred_eq] at hx
    change U x * W x = W x
    rw [hx, one_mul]
  have hBeq : ∫ x in B, U x * W x ∂ℙ = -∫ x in B, W x ∂ℙ := by
    calc ∫ x in B, U x * W x ∂ℙ = ∫ x in B, -W x ∂ℙ := by
          refine setIntegral_congr_fun hB ?_
          intro x hx
          rw [hBdef] at hx
          simp only [Set.mem_ofPred_eq] at hx
          change U x * W x = -W x
          rw [hx]
          ring
      _ = -∫ x in B, W x ∂ℙ := by rw [integral_neg]
  have hUWfinal : ∫ x, U x * W x ∂ℙ = (∫ x in A, W x ∂ℙ) - ∫ x in B, W x ∂ℙ := by
    rw [← hUWsup, hUWsplit, hAeq, hBeq]
    ring
  have ha_bound : |∫ x in A, W x ∂ℙ| ≤ 1 / 2 := by
    have h1 : |∫ x in A, W x ∂ℙ| ≤ ∫ x in A, |W x| ∂ℙ := abs_integral_le_integral_abs
    have h2 : ∫ x in A, |W x| ∂ℙ ≤ ∫ x in A, (1 : ℝ) ∂ℙ := by
      refine setIntegral_mono_on_ae hWint.abs.integrableOn (integrable_const (1 : ℝ)).integrableOn
        hA ?_
      filter_upwards [hWabs] with x hx _
      exact hx
    have h3 : ∫ x in A, (1 : ℝ) ∂ℙ = 1 / 2 := by
      rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, hU1']
      norm_num
    linarith
  have hb_bound : |∫ x in B, W x ∂ℙ| ≤ 1 / 2 := by
    have h1 : |∫ x in B, W x ∂ℙ| ≤ ∫ x in B, |W x| ∂ℙ := abs_integral_le_integral_abs
    have h2 : ∫ x in B, |W x| ∂ℙ ≤ ∫ x in B, (1 : ℝ) ∂ℙ := by
      refine setIntegral_mono_on_ae hWint.abs.integrableOn (integrable_const (1 : ℝ)).integrableOn
        hB ?_
      filter_upwards [hWabs] with x hx _
      exact hx
    have h3 : ∫ x in B, (1 : ℝ) ∂ℙ = 1 / 2 := by
      rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, hUm1']
      norm_num
    linarith
  rw [hWfinal, hUWfinal]
  exact key _ _ ha_bound hb_bound
